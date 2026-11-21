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
def PMEVTYPER_SysRegRead32_cad120e9f2cb9ca7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
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
                                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 11))))))))))))
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
                          else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 11)))))))))
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
                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 11))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 11))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegRead32_cee8110828f1d34e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
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
                                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 19))))))))))))
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
                          else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 19)))))))))
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
                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 19))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 19))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegRead32_d18be2a53d09e4e3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
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
                                   (pure (0 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 0))))))))))))
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
                           (pure (0 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 0)))))))))
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
                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 0))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegRead32_e8227d66c6f9da2f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
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
                                   (pure (13 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 13))))))))))))
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
                           (pure (13 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 13)))))))))
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
                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 13))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 13))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegRead32_e8862be86d9568ea (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
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
                                   (pure (20 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 20))))))))))))
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
                           (pure (20 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 20)))))))))
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
                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 20))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 20))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegRead32_ee465be2d00a40c6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
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
                                   (pure (4 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 4))))))))))))
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
                           (pure (4 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 4)))))))))
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
                  else (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 4))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_PMEVTYPER (← (PMEVTYPER_read 4))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMINTENCLR_SysRegRead32_f6b2fae1205a00f6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              else (R_set t (← (PMINTENCLR_read ())))))))))
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
                  else (R_set t (← (PMINTENCLR_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (PMINTENCLR_read ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMINTENSET_SysRegRead32_44a5f589c4b56eb5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              else (R_set t (← (PMINTENSET_read ())))))))))
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
                  else (R_set t (← (PMINTENSET_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (PMINTENSET_read ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMMIR_SysRegRead32_39e2ebac78343651 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              else (R_set t (__get_PMMIR (← readReg PMMIR)))))))))
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
                  else (R_set t (__get_PMMIR (← readReg PMMIR)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_PMMIR (← readReg PMMIR)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMOVSR_SysRegRead32_3a98253be39f82fc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMOVS ← (( do (pure (_get_HDFGRTR_EL2_Type_PMOVS (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMOVS == 1#1)) : Bool)
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
                                      else (R_set t (← (PMOVSR_read ()))))))))))))
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
                              else (R_set t (← (PMOVSR_read ())))))))))
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
                  else (R_set t (← (PMOVSR_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (PMOVSR_read ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMOVSSET_SysRegRead32_c13d421fe8504cc2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMOVS ← (( do (pure (_get_HDFGRTR_EL2_Type_PMOVS (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMOVS == 1#1)) : Bool)
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
                                      else (R_set t (← (PMOVSSET_read ()))))))))))))
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
                              else (R_set t (← (PMOVSSET_read ())))))))))
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
                  else (R_set t (← (PMOVSSET_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (PMOVSSET_read ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMSELR_SysRegRead32_cbb0200049a096ed (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMSELR_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMSELR_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMSELR_EL0 == 1#1)) : Bool)
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
                                      else (R_set t (__get_PMSELR (← (PMSELR_read ())))))))))))))
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
                              else (R_set t (__get_PMSELR (← (PMSELR_read ()))))))))))
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
                  else (R_set t (__get_PMSELR (← (PMSELR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_PMSELR (← (PMSELR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMUSERENR_SysRegRead32_a6257daec876c857 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMUSERENR_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMUSERENR_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMUSERENR_EL0 == 1#1)) : Bool)
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
                              else (R_set t (__get_PMUSERENR (← (PMUSERENR_read ())))))))))))
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
                              else (R_set t (__get_PMUSERENR (← (PMUSERENR_read ()))))))))))
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
                  else (R_set t (__get_PMUSERENR (← (PMUSERENR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_PMUSERENR (← (PMUSERENR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMXEVCNTR_SysRegRead32_3357c1d37107c40d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVCNTRn_EL0 == 1#1)) : Bool)
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
                                              else (R_set t (← (__get_selected_PMEVCNTR ())))))))))))))
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
                                      else (R_set t (← (__get_selected_PMEVCNTR ()))))))))))
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
                      else (R_set t (← (__get_selected_PMEVCNTR ())))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (← (__get_selected_PMEVCNTR ())))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def PMXEVTYPER_SysRegRead32_7d423ea169145383 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1)) : Bool)
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
                                                  then (R_set t (__get_PMCCFILTR (← (PMCCFILTR_read ()))))
                                                  else (R_set t (__get_PMEVTYPER (← (__get_selected_PMEVTYPER ())))))))))))))))
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
                                          then (R_set t (__get_PMCCFILTR (← (PMCCFILTR_read ()))))
                                          else (R_set t (__get_PMEVTYPER (← (__get_selected_PMEVTYPER ()))))))))))))
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
                          then (R_set t (__get_PMCCFILTR (← (PMCCFILTR_read ()))))
                          else (R_set t (__get_PMEVTYPER (← (__get_selected_PMEVTYPER ())))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) == 31) : Bool)
                      then (R_set t (__get_PMCCFILTR (← (PMCCFILTR_read ()))))
                      else (R_set t (__get_PMEVTYPER (← (__get_selected_PMEVTYPER ())))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def PRRR_SysRegRead32_4a556a683141be75 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          then
                            (do
                              if ((← (EAEisOne ())) : Bool)
                              then (R_set t (← (MAIR0_NS_read ())))
                              else (R_set t (← (PRRR_NS_read ()))))
                          else
                            (do
                              if ((← (EAEisOne ())) : Bool)
                              then (R_set t (← (MAIR0_read ())))
                              else (R_set t (← (PRRR_read ())))))))))
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
                  then (R_set t (← (MAIR0_NS_read ())))
                  else (R_set t (← (PRRR_NS_read ()))))
              else
                (do
                  if ((← (EAEisOne ())) : Bool)
                  then (R_set t (← (MAIR0_read ())))
                  else (R_set t (← (PRRR_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((← (EAEisOne ())) : Bool)
                  then
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (R_set t (← (MAIR0_S_read ())))
                      else (R_set t (← (MAIR0_NS_read ()))))
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (R_set t (← readReg PRRR_S))
                      else (R_set t (← (PRRR_NS_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def REVIDR_SysRegRead32_423676c78008247b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (← (REVIDR_read ())))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (REVIDR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (REVIDR_read ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def RMR_SysRegRead32_43cf65be6b4153a2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((←((pure ((← readReg PSTATE).EL == EL1)) <||> (do
       (pure ((← readReg PSTATE).EL == EL3))) <&&> (do
       (pure (IsHighestEL (← readReg PSTATE).EL))))) : Bool)
  then (R_set t (__get_RMR (← (RMR_read ()))))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def SCR_SysRegRead32_7742164cbe24da83 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (R_set t (__get_SCR (← readReg SCR)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SCTLR_SysRegRead32_e01eef2d08d9809d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                          then (R_set t (← (__get_SCTLR_NS (← (SCTLR_NS_read ())))))
                          else (R_set t (← (__get_SCTLR (← (SCTLR_read__2 ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (__get_SCTLR_NS (← (SCTLR_NS_read ())))))
              else (R_set t (← (__get_SCTLR (← (SCTLR_read__2 ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← (__get_SCTLR_S (← readReg SCTLR_S))))
                  else (R_set t (← (__get_SCTLR_NS (← (SCTLR_NS_read ()))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SDCR_SysRegRead32_c381e11131eb8dc4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (R_set t (__get_SDCR (← readReg SDCR)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SDER_SysRegRead32_0b9374021ce6ef0e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          else (R_set t (__get_SDER (← (SDER_read ())))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_SDER (← (SDER_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TCMTR_SysRegRead32_88195aa504d1c43a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (← readReg TCMTR))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← readReg TCMTR))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← readReg TCMTR))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TLBTR_SysRegRead32_2cb899c86cc4ff56 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (← readReg TLBTR))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← readReg TLBTR))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← readReg TLBTR))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDRPRW_SysRegRead32_2042d633efa21064 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (R_set t (← (TPIDRPRW_NS_read ())))
                  else (R_set t (← (TPIDRPRW_read ()))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (TPIDRPRW_NS_read ())))
              else (R_set t (← (TPIDRPRW_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg TPIDRPRW_S))
                  else (R_set t (← (TPIDRPRW_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDRURO_SysRegRead32_331a0b9503da6305 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_TPIDRRO_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_TPIDRRO_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TPIDRRO_EL0 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (R_set t (← (TPIDRURO_read ()))))))
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
                  then (R_set t (← (TPIDRURO_NS_read ())))
                  else (R_set t (← (TPIDRURO_read ()))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (TPIDRURO_NS_read ())))
              else (R_set t (← (TPIDRURO_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg TPIDRURO_S))
                  else (R_set t (← (TPIDRURO_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TPIDRURW_SysRegRead32_844b54dbacb876a1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_TPIDR_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_TPIDR_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_TPIDR_EL0 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else (R_set t (← (TPIDRURW_read ()))))))
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
                  then (R_set t (← (TPIDRURW_NS_read ())))
                  else (R_set t (← (TPIDRURW_read ()))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (TPIDRURW_NS_read ())))
              else (R_set t (← (TPIDRURW_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg TPIDRURW_S))
                  else (R_set t (← (TPIDRURW_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TRFCR_SysRegRead32_4539d9acce538415 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      else (R_set t (__get_TRFCR (← (TRFCR_read ()))))))))))))
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
                          else (R_set t (__get_TRFCR (← (TRFCR_read ()))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SDCR_TTRF == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (__get_TRFCR (← (TRFCR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBCR2_SysRegRead32_9005164b21d17bb0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T2 ← (( do (pure (_get_HSTR_EL2_Type_T2 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T2 ← (( do (pure (_get_HSTR_Type_T2 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                          then (R_set t (__get_TTBCR2_NS (← (TTBCR2_NS_read ()))))
                          else (R_set t (__get_TTBCR2 (← (TTBCR2_read ())))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (__get_TTBCR2_NS (← (TTBCR2_NS_read ()))))
              else (R_set t (__get_TTBCR2 (← (TTBCR2_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (__get_TTBCR2_S (← readReg TTBCR2_S)))
                  else (R_set t (__get_TTBCR2_NS (← (TTBCR2_NS_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBCR_SysRegRead32_254407681da2385f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T2 ← (( do (pure (_get_HSTR_EL2_Type_T2 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T2 ← (( do (pure (_get_HSTR_Type_T2 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                          then (R_set t (← (TTBCR_NS_read ())))
                          else (R_set t (← (TTBCR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (TTBCR_NS_read ())))
              else (R_set t (← (TTBCR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg TTBCR_S))
                  else (R_set t (← (TTBCR_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR0_SysRegRead32_ba6eb6544c3c44a1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T2 ← (( do (pure (_get_HSTR_EL2_Type_T2 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T2 ← (( do (pure (_get_HSTR_Type_T2 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                          then (R_set t (Sail.BitVec.extractLsb (← readReg TTBR0_NS) 31 0))
                          else (R_set t (Sail.BitVec.extractLsb (← (TTBR0_read ())) 31 0)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (Sail.BitVec.extractLsb (← readReg TTBR0_NS) 31 0))
              else (R_set t (Sail.BitVec.extractLsb (← (TTBR0_read ())) 31 0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (Sail.BitVec.extractLsb (← readReg TTBR0_S) 31 0))
                  else (R_set t (Sail.BitVec.extractLsb (← readReg TTBR0_NS) 31 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def TTBR1_SysRegRead32_bbb7c8fdac68a224 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T2 ← (( do (pure (_get_HSTR_EL2_Type_T2 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T2 ← (( do (pure (_get_HSTR_Type_T2 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                          then (R_set t (Sail.BitVec.extractLsb (← readReg TTBR1_NS) 31 0))
                          else (R_set t (Sail.BitVec.extractLsb (← (TTBR1_read ())) 31 0)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (Sail.BitVec.extractLsb (← readReg TTBR1_NS) 31 0))
              else (R_set t (Sail.BitVec.extractLsb (← (TTBR1_read ())) 31 0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (Sail.BitVec.extractLsb (← readReg TTBR1_S) 31 0))
                  else (R_set t (Sail.BitVec.extractLsb (← readReg TTBR1_NS) 31 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VBAR_SysRegRead32_cbb282dd5c9d55ce (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  then (R_set t (__get_VBAR_NS (← (VBAR_NS_read ()))))
                  else (R_set t (__get_VBAR (← (VBAR_read__2 ())))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (__get_VBAR_NS (← (VBAR_NS_read ()))))
              else (R_set t (__get_VBAR (← (VBAR_read__2 ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (__get_VBAR_S (← readReg VBAR_S)))
                  else (R_set t (__get_VBAR_NS (← (VBAR_NS_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VDFSR_SysRegRead32_0530b84beb618cd2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (R_set t (__get_VDFSR (← (VDFSR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_VDFSR (← (VDFSR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VDISR_SysRegRead32_1bd7b149463ed2f1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (R_set t (__get_VDISR (← (VDISR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_VDISR (← (VDISR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VMPIDR_SysRegRead32_2f5b95225c646973 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
                  then (R_set t (Sail.BitVec.extractLsb (__get_VMPIDR_EL2 (← readReg VMPIDR_EL2)) 31 0))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)))) : Bool)
                      then (R_set t (__get_VMPIDR (← (VMPIDR_read ()))))
                      else (R_set t (__get_MPIDR (← (MPIDR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (__get_MPIDR (← (MPIDR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_MPIDR (← (MPIDR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VMPIDR_SysRegRead32_e5aa49e29a7b94ba (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (R_set t (__get_VMPIDR (← (VMPIDR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (R_set t (__get_MPIDR (← (MPIDR_read ()))))
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (R_set t (__get_VMPIDR (← (VMPIDR_read ()))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VPIDR_SysRegRead32_4e4cbaa7ba154382 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (R_set t (← (VPIDR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then (R_set t (← (MIDR_read ())))
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (R_set t (← (VPIDR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def VTCR_SysRegRead32_23b906196b602c93 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (R_set t (__get_VTCR (← (VTCR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_VTCR (← (VTCR_read ())))))
              else (pure ()))))

def GetNreg (_ : Unit) : SailM Int := do
  let nreg ← (( do (undefined_int ()) ) : SailM Int )
  let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  let nreg ← (( do
    if (((((Sail.BitVec.extractLsb instr 31 28) != 0b1111#4) && ((Sail.BitVec.extractLsb instr 27 24) == 0b1110#4)) && ((BitVec.join1 [(BitVec.access instr 4)]) == 1#1)) : Bool)
    then (pure 1)
    else
      (do
        if ((((Sail.BitVec.extractLsb instr 31 28) != 0b1111#4) && ((Sail.BitVec.extractLsb instr 27 21) == 0b1100010#7)) : Bool)
        then (pure 2)
        else
          (do
            if (((((Sail.BitVec.extractLsb instr 31 28) != 0b1111#4) && ((Sail.BitVec.extractLsb instr 27 25) == 0b110#3)) && ((BitVec.join1 [(BitVec.access instr 22)]) == 0#1)) : Bool)
            then (pure 0)
            else
              (do
                sail_assert false "src/sysregs.sail:1400.20-1400.21"
                throw Error.Exit))) ) : SailM Int )
  let nreg := nreg
  (pure nreg)

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegRead64_2b274c768298c3f9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR00_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR00_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (0 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (0 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if ((((←((EL2Enabled ()) <&&> (do
                                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR00_EL0 == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                      else
                                        (do
                                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 0) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 0) 31 0)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1)))))))))))
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
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (0 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)))) && (0 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 0) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 0) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 0) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 0) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 0) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 0) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegRead64_58cd2445e81e8975 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR03_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR03_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (3 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (3 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if ((((←((EL2Enabled ()) <&&> (do
                                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR03_EL0 == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                      else
                                        (do
                                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 3) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 3) 31 0)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1)))))))))))
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
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (3 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)))) && (3 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 3) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 3) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 3) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 3) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 3) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 3) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegRead64_66e81afe82d2c192 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR01_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR01_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (1 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (1 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if ((((←((EL2Enabled ()) <&&> (do
                                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR01_EL0 == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                      else
                                        (do
                                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 1) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 1) 31 0)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1)))))))))))
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
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (1 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)))) && (1 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 1) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 1) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 1) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 1) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 1) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 1) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegRead64_bf8f308b8b559115 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T0 ← (( do (pure (_get_HSTR_EL2_Type_T0 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T0 ← (( do (pure (_get_HSTR_Type_T0 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR02_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR02_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (2 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (2 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if ((((←((EL2Enabled ()) <&&> (do
                                           (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR02_EL0 == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                      else
                                        (do
                                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 2) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 2) 31 0)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1)))))))))))
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
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (2 <b 8)) && (__HSTR_EL2_T0 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)))) && (2 <b 8)) && (__HSTR_T0 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 2) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 2) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 2) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 2) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 2) 63 32), (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg AMEVCNTR0) 2) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_065fe37bc5a680bd (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR113_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR113_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 13))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (13 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)))) && (13 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR113_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                          else
                                            (do
                                              if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                              then
                                                (do
                                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                  (R_set t2 __tup_0)
                                                  (R_set t __tup_1))
                                              else
                                                (do
                                                  if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1))
                                                  else
                                                    (do
                                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 13)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 13)) 31 0)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1)))))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))))) && (13 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (13 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                             (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                                 (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 13)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 13)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 13)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 13)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 13)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 13)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_132f33bfb64bea99 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR11_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR11_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if ((((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR11_EL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 1)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 1)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1)))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                         (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 1)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 1)) 31 0)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 1)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 1)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 1)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 1)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_13f84beb778d3114 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR12_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR12_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if ((((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR12_EL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 2)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 2)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1)))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                         (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 2)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 2)) 31 0)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 2)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 2)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 2)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 2)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_141e5d18f9a75c13 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR17_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR17_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 7))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if ((((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR17_EL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 7)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 7)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1)))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                         (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 7)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 7)) 31 0)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 7)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 7)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 7)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 7)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_2d5e01434567b282 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR15_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR15_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 5))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if ((((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR15_EL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 5)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 5)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1)))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                         (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 5)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 5)) 31 0)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 5)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 5)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 5)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 5)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_4cd25036d674f8ac (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR19_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR19_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 9))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (9 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)))) && (9 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR19_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                          else
                                            (do
                                              if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                              then
                                                (do
                                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                  (R_set t2 __tup_0)
                                                  (R_set t __tup_1))
                                              else
                                                (do
                                                  if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1))
                                                  else
                                                    (do
                                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 9)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 9)) 31 0)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1)))))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))))) && (9 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (9 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                             (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                                 (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 9)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 9)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 9)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 9)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 9)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 9)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_4e22e3365cdbab7d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR13_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR13_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 3))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if ((((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR13_EL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 3)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 3)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1)))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                         (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 3)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 3)) 31 0)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 3)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 3)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 3)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 3)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_51a9ce69caa26d97 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR115_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR115_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 15))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (15 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)))) && (15 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR115_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                          else
                                            (do
                                              if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                              then
                                                (do
                                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                  (R_set t2 __tup_0)
                                                  (R_set t __tup_1))
                                              else
                                                (do
                                                  if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1))
                                                  else
                                                    (do
                                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 15)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 15)) 31 0)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1)))))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))))) && (15 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (15 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                             (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                                 (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 15)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 15)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 15)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 15)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 15)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 15)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_6f64074808614759 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR16_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR16_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 6))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if ((((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR16_EL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 6)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 6)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1)))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                         (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 6)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 6)) 31 0)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 6)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 6)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 6)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 6)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_839ed88b8f796549 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR111_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR111_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 11))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (11 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)))) && (11 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR111_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                          else
                                            (do
                                              if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                              then
                                                (do
                                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                  (R_set t2 __tup_0)
                                                  (R_set t __tup_1))
                                              else
                                                (do
                                                  if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1))
                                                  else
                                                    (do
                                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 11)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 11)) 31 0)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1)))))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))))) && (11 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (11 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                             (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                                 (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 11)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 11)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 11)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 11)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 11)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 11)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_9c104b95f67d3b22 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR18_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR18_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 8))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (8 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)))) && (8 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR18_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                          else
                                            (do
                                              if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                              then
                                                (do
                                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                  (R_set t2 __tup_0)
                                                  (R_set t __tup_1))
                                              else
                                                (do
                                                  if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1))
                                                  else
                                                    (do
                                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 8)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 8)) 31 0)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1)))))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))))) && (8 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (8 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                             (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                                 (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 8)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 8)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 8)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 8)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 8)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 8)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_a118420696d1228f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR10_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR10_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 0))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if ((((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR10_EL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 0)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 0)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1)))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                         (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 0)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 0)) 31 0)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 0)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 0)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 0)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 0)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_cdf416f7d354cbf5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR114_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR114_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 14))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (14 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)))) && (14 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR114_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                          else
                                            (do
                                              if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                              then
                                                (do
                                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                  (R_set t2 __tup_0)
                                                  (R_set t __tup_1))
                                              else
                                                (do
                                                  if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1))
                                                  else
                                                    (do
                                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 14)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 14)) 31 0)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1)))))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))))) && (14 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (14 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                             (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                                 (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 14)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 14)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 14)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 14)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 14)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 14)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_d4ffe491a2456c2b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR112_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR112_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 12))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (12 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)))) && (12 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR112_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                          else
                                            (do
                                              if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                              then
                                                (do
                                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                  (R_set t2 __tup_0)
                                                  (R_set t __tup_1))
                                              else
                                                (do
                                                  if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1))
                                                  else
                                                    (do
                                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 12)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 12)) 31 0)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1)))))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))))) && (12 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (12 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                             (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                                 (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 12)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 12)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 12)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 12)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 12)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 12)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_eefece484f7466c9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR14_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR14_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 4))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if ((((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR14_EL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 4)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 4)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1)))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                         (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 4)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 4)) 31 0)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 4)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 4)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 4)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 4)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegRead64_fa3226080978524b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EL0_EN ← (( do (pure (_get_AMUSERENR_EL0_Type_EN (← readReg AMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __AMUSERENR_EN ← (( do (pure (_get_AMUSERENR_Type_EN (← (AMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HAFGRTR_EL2_AMEVCNTR110_EL0 ← (( do (pure (_get_HAFGRTR_EL2_Type_AMEVCNTR110_EL0 (← readReg HAFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __AMCR_EL0_CG1RZ ← (( do (pure (_get_AMCR_EL0_Type_CG1RZ (← readReg AMCR_EL0))) ) : SailM (BitVec 1) )
  let __AMCR_CG1RZ ← (( do (pure (_get_AMCR_Type_CG1RZ (← (AMCR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 10))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__AMUSERENR_EN == 0#1)) : Bool)
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
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (10 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)))) && (10 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                                  else
                                    (do
                                      if ((((←((EL2Enabled ()) <&&> (do
                                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HAFGRTR_EL2_AMEVCNTR110_EL0 == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                          else
                                            (do
                                              if (((← (HaveAArch64 ())) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                              then
                                                (do
                                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                  (R_set t2 __tup_0)
                                                  (R_set t __tup_1))
                                              else
                                                (do
                                                  if (((! (← (HaveAArch64 ()))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1))
                                                  else
                                                    (do
                                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 10)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 10)) 31 0)))
                                                      (R_set t2 __tup_0)
                                                      (R_set t __tup_1)))))))))))))
      else
        (do
          if (((← readReg PSTATE).EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))))) && (10 ≥b 8)) && (__HSTR_EL2_T5 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)))) && (10 ≥b 8)) && (__HSTR_T5 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CPTR_EL2_TAM == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCPTR_TAM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                             (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                                      then
                                        (do
                                          let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1))
                                      else
                                        (do
                                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                                 (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                                          then
                                            (do
                                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))
                                          else
                                            (do
                                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 10)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 10)) 31 0)))
                                              (R_set t2 __tup_0)
                                              (R_set t __tup_1))))))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL2) : Bool)
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                 (HaveAArch64 ())))) && (__AMCR_EL0_CG1RZ == 1#1)) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              if (((←((pure (! (IsHighestEL (← readReg PSTATE).EL))) <&&> (do
                                     (pure (! (← (HaveAArch64 ()))))))) && (__AMCR_CG1RZ == 1#1)) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) := ((Zeros (n := 32)), (Zeros (n := 32)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 10)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 10)) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))
              else
                (do
                  if (((← readReg PSTATE).EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (AMEVCNTR1_read 10)) 63 32), (Sail.BitVec.extractLsb (← (AMEVCNTR1_read 10)) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTHPS_CVAL_SysRegRead64_aa5fa6170d1a3db5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                              then
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg CNTHPS_CVAL_EL2) 63 32), (Sail.BitVec.extractLsb (← readReg CNTHPS_CVAL_EL2) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                                  then
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg CNTHP_CVAL_EL2) 63 32), (Sail.BitVec.extractLsb (← readReg CNTHP_CVAL_EL2) 31 0)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))
                                  else
                                    (do
                                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTP_CVAL_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTP_CVAL_read ())) 31 0)))
                                      (R_set t2 __tup_0)
                                      (R_set t __tup_1))))))))))
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
                      then
                        (do
                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTP_CVAL_NS_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTP_CVAL_NS_read ())) 31 0)))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))
                      else
                        (do
                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTP_CVAL_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTP_CVAL_read ())) 31 0)))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTP_CVAL_NS_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTP_CVAL_NS_read ())) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTP_CVAL_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTP_CVAL_read ())) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg CNTP_CVAL_S) 63 32), (Sail.BitVec.extractLsb (← readReg CNTP_CVAL_S) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTP_CVAL_NS_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTP_CVAL_NS_read ())) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTHP_CVAL_SysRegRead64_bedb5ea1dc82962f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then
            (do
              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTHP_CVAL_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTHP_CVAL_read ())) 31 0)))
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTHP_CVAL_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTHP_CVAL_read ())) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTHV_CVAL_SysRegRead64_7bf312f271feb72e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                      then
                        (do
                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg CNTHVS_CVAL_EL2) 63 32), (Sail.BitVec.extractLsb (← readReg CNTHVS_CVAL_EL2) 31 0)))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg CNTHV_CVAL_EL2) 63 32), (Sail.BitVec.extractLsb (← readReg CNTHV_CVAL_EL2) 31 0)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTV_CVAL_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTV_CVAL_read ())) 31 0)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else
            (do
              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTV_CVAL_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTV_CVAL_read ())) 31 0)))
              (R_set t2 __tup_0)
              (R_set t __tup_1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTV_CVAL_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTV_CVAL_read ())) 31 0)))
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTV_CVAL_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTV_CVAL_read ())) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTPCT_SysRegRead64_7dc4fea5bbad7fe9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PCTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PCTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTKCTL_PL0PCTEN ← (( do (pure (_get_CNTKCTL_Type_PL0PCTEN (← (CNTKCTL_read__1 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCTEN ← (( do
    (pure (BitVec.slice (← readReg CNTHCTL_EL2)
        (← (do
          if ((←((IsFeatureImplemented FEAT_VHE) <&&> (do
               (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))) : Bool)
          then (pure 10)
          else (pure 0))) 1)) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PCTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PCTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_PL1PCTEN ← (( do (pure (_get_CNTHCTL_Type_PL1PCTEN (← (CNTHCTL_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ECVEn ← (( do (pure (_get_SCR_EL3_Type_ECVEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_ECV ← (( do (pure (_get_CNTHCTL_EL2_Type_ECV (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__CNTKCTL_EL1_EL0PCTEN == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__CNTKCTL_PL0PCTEN == 0#1)) : Bool)
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
                       (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 0#1)) && (__CNTHCTL_EL2_EL1PCTEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PCTEN == 0#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PCTEN == 0#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__CNTHCTL_PL1PCTEN == 0#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                          else
                            (do
                              if ((←((pure (((←((IsFeatureImplemented FEAT_ECV) <&&> (do (EL2Enabled ())) <&&> (do (pure (! (← (ELUsingAArch32 EL2))))))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) : Bool)
                              then
                                (do
                                  let (__tup_0, __tup_1) ← do (Split ((← (PhysicalCountInt ())) - (← readReg CNTPOFF_EL2)) 32)
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (Split (← (PhysicalCountInt ())) 32)
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CNTHCTL_EL2_EL1PCTEN == 0#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__CNTHCTL_PL1PCTEN == 0#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
              else
                (do
                  if ((((←((IsFeatureImplemented FEAT_ECV) <&&> (do
                           (EL2Enabled ())) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1)) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (Split ((← (PhysicalCountInt ())) - (← readReg CNTPOFF_EL2)) 32)
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (Split (← (PhysicalCountInt ())) 32)
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let (__tup_0, __tup_1) ← do (Split (← (PhysicalCountInt ())) 32)
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (Split (← (PhysicalCountInt ())) 32)
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTVCT_SysRegRead64_6e373436952b9ca9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VCTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VCTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTKCTL_PL0VCTEN ← (( do (pure (_get_CNTKCTL_Type_PL0VCTEN (← (CNTKCTL_read__1 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VCTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VCTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVCT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVCT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__CNTKCTL_EL1_EL0VCTEN == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__CNTKCTL_PL0VCTEN == 0#1)) : Bool)
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
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VCTEN == 0#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVCT == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL2)) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure (! (← (EL2Enabled ())))) <||> (do
                             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2)))))) : Bool)
                      then
                        (do
                          let (__tup_0, __tup_1) ← do (Split ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)) 32)
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))
                      else
                        (do
                          if ((←((pure (HaveEL EL2)) <&&> (do
                               (ELUsingAArch32 EL2)))) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) ← do (Split ((← (PhysicalCountInt ())) - (← (CNTVOFF_read ()))) 32)
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              let (__tup_0, __tup_1) ← do (Split (← (PhysicalCountInt ())) 32)
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CNTHCTL_EL2_EL1TVCT == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
          else
            (do
              if ((←((pure (HaveEL EL2)) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (Split ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)) 32)
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else
                (do
                  if ((←((pure (HaveEL EL2)) <&&> (do
                       (ELUsingAArch32 EL2)))) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (Split ((← (PhysicalCountInt ())) - (← (CNTVOFF_read ()))) 32)
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (Split (← (PhysicalCountInt ())) 32)
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let (__tup_0, __tup_1) ← do (Split ((← (PhysicalCountInt ())) - (← (CNTVOFF_read ()))) 32)
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((HaveEL EL2) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (Split ((← (PhysicalCountInt ())) - (← (CNTVOFF_read ()))) 32)
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (Split (← (PhysicalCountInt ())) 32)
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def CNTVOFF_SysRegRead64_66c4d48806fce48e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then
            (do
              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTVOFF_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTVOFF_read ())) 31 0)))
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (CNTVOFF_read ())) 63 32), (Sail.BitVec.extractLsb (← (CNTVOFF_read ())) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def DBGDRAR_SysRegRead64_89f87ddb7d53b509 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __DBGDSCRext_UDCCdis ← (( do (pure (_get_DBGDSCRext_Type_UDCCdis (← (DBGDSCRext_read ())))) ) : SailM (BitVec 1) )
  if ((←((Halted ()) <&&> (do
       (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
  then
    (do
      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (DBGDRAR_read ())) 63 32), (Sail.BitVec.extractLsb (← (DBGDRAR_read ())) 31 0)))
      (R_set t2 __tup_0)
      (R_set t __tup_1))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__MDSCR_EL1_TDCC == 1#1)) : Bool)
              then
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x0C#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__DBGDSCRext_UDCCdis == 1#1)) : Bool)
                  then
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)) <&&> (do
                               (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1))))) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do
                             (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDRA (← readReg MDCR_EL2))) != 0b00#2)))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)) <&&> (do
                               (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1)) <||> (do
                                 (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDRA (← (HDCR_read ())))) != 0b00#2)))))) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8)))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (DBGDRAR_read ())) 63 32), (Sail.BitVec.extractLsb (← (DBGDRAR_read ())) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
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
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDRA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDRA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8)))
                          else
                            (do
                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (DBGDRAR_read ())) 63 32), (Sail.BitVec.extractLsb (← (DBGDRAR_read ())) 31 0)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))))))
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8)))
                      else
                        (do
                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (DBGDRAR_read ())) 63 32), (Sail.BitVec.extractLsb (← (DBGDRAR_read ())) 31 0)))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (DBGDRAR_read ())) 63 32), (Sail.BitVec.extractLsb (← (DBGDRAR_read ())) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def DBGDSAR_SysRegRead64_2f971e6eb001648b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __DBGDSCRext_UDCCdis ← (( do (pure (_get_DBGDSCRext_Type_UDCCdis (← (DBGDSCRext_read ())))) ) : SailM (BitVec 1) )
  if ((←((Halted ()) <&&> (do
       (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
  then
    (do
      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg DBGDSAR) 63 32), (Sail.BitVec.extractLsb (← readReg DBGDSAR) 31 0)))
      (R_set t2 __tup_0)
      (R_set t __tup_1))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((! (← (ELUsingAArch32 EL1))) && (__MDSCR_EL1_TDCC == 1#1)) : Bool)
              then
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x0C#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__DBGDSCRext_UDCCdis == 1#1)) : Bool)
                  then
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)) <&&> (do
                               (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1))))) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8))
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do
                             (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDRA (← readReg MDCR_EL2))) != 0b00#2)))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)) <&&> (do
                               (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1)) <||> (do
                                 (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDRA (← (HDCR_read ())))) != 0b00#2)))))) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8)))
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg DBGDSAR) 63 32), (Sail.BitVec.extractLsb (← readReg DBGDSAR) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
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
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDRA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDRA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8)))
                          else
                            (do
                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg DBGDSAR) 63 32), (Sail.BitVec.extractLsb (← readReg DBGDSAR) 31 0)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))))))
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
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8)))
                      else
                        (do
                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg DBGDSAR) 63 32), (Sail.BitVec.extractLsb (← readReg DBGDSAR) 31 0)))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg DBGDSAR) 63 32), (Sail.BitVec.extractLsb (← readReg DBGDSAR) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure ())))))

/-- Type quantifiers: t : Int, t2 : Int -/
def HTTBR_SysRegRead64_5b679aebf4474d8a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then
            (do
              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg HTTBR) 63 32), (Sail.BitVec.extractLsb (← readReg HTTBR) 31 0)))
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg HTTBR) 63 32), (Sail.BitVec.extractLsb (← readReg HTTBR) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def PAR_SysRegRead64_bd143a1fe560ae4b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg PAR_NS) 63 32), (Sail.BitVec.extractLsb (← readReg PAR_NS) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (PAR_read ())) 63 32), (Sail.BitVec.extractLsb (← (PAR_read ())) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg PAR_NS) 63 32), (Sail.BitVec.extractLsb (← readReg PAR_NS) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (PAR_read ())) 63 32), (Sail.BitVec.extractLsb (← (PAR_read ())) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg PAR_S) 63 32), (Sail.BitVec.extractLsb (← readReg PAR_S) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg PAR_NS) 63 32), (Sail.BitVec.extractLsb (← readReg PAR_NS) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def PMCCNTR_SysRegRead64_1cf48d19bc879bd3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_PMCCNTR_EL0 ← (( do (pure (_get_HDFGRTR_EL2_Type_PMCCNTR_EL0 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                 (pure (((_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0)) +++ ((_get_PMUSERENR_EL0_Type_CR (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)))) == 0b000#3))) <||> (do
                 (pure (! (← (IsFeatureImplemented FEAT_PMUv3p9)))) <&&> (do
                   (pure (((_get_PMUSERENR_EL0_Type_CR (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) == 0b00#2))))))) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8)))
          else
            (do
              if ((←((ELUsingAArch32 EL1) <&&> (do
                   (pure (((_get_PMUSERENR_Type_CR (← (PMUSERENR_read ()))) +++ (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) == 0b00#2))))) : Bool)
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
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_PMCCNTR_EL0 == 1#1)) : Bool)
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
                                      else
                                        (do
                                          let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (PMCCNTR_read ())) 63 32), (Sail.BitVec.extractLsb (← (PMCCNTR_read ())) 31 0)))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1)))))))))))
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
                              else
                                (do
                                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (PMCCNTR_read ())) 63 32), (Sail.BitVec.extractLsb (← (PMCCNTR_read ())) 31 0)))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
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
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (PMCCNTR_read ())) 63 32), (Sail.BitVec.extractLsb (← (PMCCNTR_read ())) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (PMCCNTR_read ())) 63 32), (Sail.BitVec.extractLsb (← (PMCCNTR_read ())) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_SysRegRead64_9396816aa24cfa90 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T2 ← (( do (pure (_get_HSTR_EL2_Type_T2 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T2 ← (( do (pure (_get_HSTR_Type_T2 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TRVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TRVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg TTBR0_NS) 63 32), (Sail.BitVec.extractLsb (← readReg TTBR0_NS) 31 0)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (TTBR0_read ())) 63 32), (Sail.BitVec.extractLsb (← (TTBR0_read ())) 31 0)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg TTBR0_NS) 63 32), (Sail.BitVec.extractLsb (← readReg TTBR0_NS) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (TTBR0_read ())) 63 32), (Sail.BitVec.extractLsb (← (TTBR0_read ())) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg TTBR0_S) 63 32), (Sail.BitVec.extractLsb (← readReg TTBR0_S) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg TTBR0_NS) 63 32), (Sail.BitVec.extractLsb (← readReg TTBR0_NS) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_SysRegRead64_6988488afc2dce1a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T2 ← (( do (pure (_get_HSTR_EL2_Type_T2 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T2 ← (( do (pure (_get_HSTR_Type_T2 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TRVM == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_TRVM == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then
                            (do
                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg TTBR1_NS) 63 32), (Sail.BitVec.extractLsb (← readReg TTBR1_NS) 31 0)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))
                          else
                            (do
                              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (TTBR1_read ())) 63 32), (Sail.BitVec.extractLsb (← (TTBR1_read ())) 31 0)))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg TTBR1_NS) 63 32), (Sail.BitVec.extractLsb (← readReg TTBR1_NS) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else
                (do
                  let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← (TTBR1_read ())) 63 32), (Sail.BitVec.extractLsb (← (TTBR1_read ())) 31 0)))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg TTBR1_S) 63 32), (Sail.BitVec.extractLsb (← readReg TTBR1_S) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg TTBR1_NS) 63 32), (Sail.BitVec.extractLsb (← readReg TTBR1_NS) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def VTTBR_SysRegRead64_aec948eb11ac7d09 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then
            (do
              let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg VTTBR) 63 32), (Sail.BitVec.extractLsb (← readReg VTTBR) 31 0)))
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      let (__tup_0, __tup_1) ← do (pure ((Sail.BitVec.extractLsb (← readReg VTTBR) 63 32), (Sail.BitVec.extractLsb (← readReg VTTBR) 31 0)))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ACTLR2_SysRegWrite32_282be907bf9b1055 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          then (ACTLR2_NS_write (← (R_read t)))
                          else (ACTLR2_write (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (ACTLR2_NS_write (← (R_read t)))
              else (ACTLR2_write (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg ACTLR2_S (← (R_read t))
                  else (ACTLR2_NS_write (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ACTLR_SysRegWrite32_5d9dcbc79ea74dc0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          then (ACTLR_NS_write (← (R_read t)))
                          else (ACTLR_write (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (ACTLR_NS_write (← (R_read t)))
              else (ACTLR_write (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg ACTLR_S (← (R_read t))
                  else (ACTLR_NS_write (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ADFSR_SysRegWrite32_750ccc4b21c14510 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                          then (ADFSR_NS_write (← (R_read t)))
                          else (ADFSR_write (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (ADFSR_NS_write (← (R_read t)))
              else (ADFSR_write (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg ADFSR_S (← (R_read t))
                  else (ADFSR_NS_write (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AIFSR_SysRegWrite32_0ca6e826bb64fe73 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                          then (AIFSR_NS_write (← (R_read t)))
                          else (AIFSR_write (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (AIFSR_NS_write (← (R_read t)))
              else (AIFSR_write (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg AIFSR_S (← (R_read t))
                  else (AIFSR_NS_write (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR0_SysRegWrite32_c80dd68970641167 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          then (AMAIR0_NS_write (← (R_read t)))
                          else (AMAIR0_write (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (AMAIR0_NS_write (← (R_read t)))
              else (AMAIR0_write (← (R_read t))))
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
                          then writeReg AMAIR0_S (← (R_read t))
                          else (AMAIR0_NS_write (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMAIR1_SysRegWrite32_3836d7092d627787 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          then (AMAIR1_NS_write (← (R_read t)))
                          else (AMAIR1_write (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (AMAIR1_NS_write (← (R_read t)))
              else (AMAIR1_write (← (R_read t))))
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
                          then writeReg AMAIR1_S (← (R_read t))
                          else (AMAIR1_NS_write (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def AMCNTENCLR0_SysRegWrite32_38bf5168732af700 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
      else
        (do
          if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
          then (AMCNTENCLR0_write (Mk_AMCNTENCLR0_Type (← (R_read t))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit)))

/-- Type quantifiers: t : Int -/
def AMCNTENCLR1_SysRegWrite32_54f7ea48fcecb714 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
      else
        (do
          if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
          then (AMCNTENCLR1_write (Mk_AMCNTENCLR1_Type (← (R_read t))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit)))

/-- Type quantifiers: t : Int -/
def AMCNTENSET0_SysRegWrite32_e19916620d98350a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
      else
        (do
          if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
          then (AMCNTENSET0_write (Mk_AMCNTENSET0_Type (← (R_read t))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit)))

/-- Type quantifiers: t : Int -/
def AMCNTENSET1_SysRegWrite32_c9fde2d74a2eae8e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
      else
        (do
          if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
          then (AMCNTENSET1_write (Mk_AMCNTENSET1_Type (← (R_read t))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit)))

/-- Type quantifiers: t : Int -/
def AMCR_SysRegWrite32_0a36aa89c00db4ab (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
      else
        (do
          if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
          then (AMCR_write (Mk_AMCR_Type (← (R_read t))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit)))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_10f3aef13e8663a1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 1 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_1c15a0e3b00864c2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 7))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 7 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_3549526a1f7ad5a9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 4))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 4 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_381d8337f3d30ba8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 5))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 5 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_3f6816ffcd57dccb (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 13))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 13 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_405b1a2a28f91a31 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 10))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 10 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_4c73d953aff0e20b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 15))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 15 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_4f4eada85dcde70a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 0))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 0 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_5157ae2713cc2d9d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 9))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 9 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_5a1635be7bbcd05b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 11))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 11 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_a868a5149842a50f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 12))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 12 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_c08be1aaf0c6ac78 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 8))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 8 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_cb60b5ebc90e745e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 14))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 14 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_d066b294b71fc9c6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 2 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_d612c920e0f1e095 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 6))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 6 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_fe1a95b5287339db (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((! (← (IsG1ActivityMonitorImplemented 3))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T13 == 1#1)) : Bool)
      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
      else
        (do
          if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (ELUsingAArch32 EL2)))) && (__HSTR_T13 == 1#1)) : Bool)
          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
          else
            (do
              if ((←((pure (IsHighestEL (← readReg PSTATE).EL)) <&&> (do
                   (pure (! (← (__IMPDEF_boolean "AMEVCNTR1[m] is fixed"))))))) : Bool)
              then (AMEVTYPER1_set 3 (Mk_AMEVTYPER1_Type (← (R_read t))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))))

/-- Type quantifiers: t : Int -/
def AMUSERENR_SysRegWrite32_2ac4dae68b0ff25f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CPTR_EL3_TAM ← (( do (pure (_get_CPTR_EL3_Type_TAM (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TAM ← (( do (pure (_get_CPTR_EL2_Type_TAM (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __HCPTR_TAM ← (( do (pure (_get_HCPTR_Type_TAM (← (HCPTR_read ())))) ) : SailM (BitVec 1) )
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
                              else (AMUSERENR_write (Mk_AMUSERENR_Type (← (R_read t))))))))))
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
                  else (AMUSERENR_write (Mk_AMUSERENR_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AMUSERENR_write (Mk_AMUSERENR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS12NSOPR_SysRegWrite32_29b73e1bf71ad72e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
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
          then (AArch32_AT (← (R_read t)) TranslationStage_12 EL1 ATAccess_Read)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_AT (← (R_read t)) TranslationStage_12 EL1 ATAccess_Read)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS12NSOPW_SysRegWrite32_ed16ee3eca6aefe5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
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
          then (AArch32_AT (← (R_read t)) TranslationStage_12 EL1 ATAccess_Write)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_AT (← (R_read t)) TranslationStage_12 EL1 ATAccess_Write)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS12NSOUR_SysRegWrite32_c89f9455fa8ec3dc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
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
          then (AArch32_AT (← (R_read t)) TranslationStage_12 EL0 ATAccess_Read)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_AT (← (R_read t)) TranslationStage_12 EL0 ATAccess_Read)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS12NSOUW_SysRegWrite32_67f712d7e127f198 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
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
          then (AArch32_AT (← (R_read t)) TranslationStage_12 EL0 ATAccess_Write)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_AT (← (R_read t)) TranslationStage_12 EL0 ATAccess_Write)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS1CPRP_SysRegWrite32_42119243d95c582f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_ReadPAN)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_ReadPAN)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (AArch32_AT (← (R_read t)) TranslationStage_1 EL3 ATAccess_ReadPAN)
                  else (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_ReadPAN))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS1CPR_SysRegWrite32_810a4a7e2785c9d5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_Read)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_Read)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (AArch32_AT (← (R_read t)) TranslationStage_1 EL3 ATAccess_Read)
                  else (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_Read))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS1CPWP_SysRegWrite32_9f529f7ec0bf0000 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_WritePAN)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_WritePAN)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (AArch32_AT (← (R_read t)) TranslationStage_1 EL3 ATAccess_WritePAN)
                  else (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_WritePAN))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS1CPW_SysRegWrite32_c343c707514145e0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_Write)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_Write)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (AArch32_AT (← (R_read t)) TranslationStage_1 EL3 ATAccess_Write)
                  else (AArch32_AT (← (R_read t)) TranslationStage_1 EL1 ATAccess_Write))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS1CUR_SysRegWrite32_592c369d819e223e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (AArch32_AT (← (R_read t)) TranslationStage_1 EL0 ATAccess_Read)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_AT (← (R_read t)) TranslationStage_1 EL0 ATAccess_Read)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_AT (← (R_read t)) TranslationStage_1 EL0 ATAccess_Read)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS1CUW_SysRegWrite32_eb4fd0807cfcfcfb (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (AArch32_AT (← (R_read t)) TranslationStage_1 EL0 ATAccess_Write)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_AT (← (R_read t)) TranslationStage_1 EL0 ATAccess_Write)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_AT (← (R_read t)) TranslationStage_1 EL0 ATAccess_Write)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS1HR_SysRegWrite32_dc67c53b4eef830a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_AT (← (R_read t)) TranslationStage_1 EL2 ATAccess_Read)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_AT (← (R_read t)) TranslationStage_1 EL2 ATAccess_Read)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ATS1HW_SysRegWrite32_6bb51bbf34dda57b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_AT (← (R_read t)) TranslationStage_1 EL2 ATAccess_Write)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_AT (← (R_read t)) TranslationStage_1 EL2 ATAccess_Write)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BPIALLIS_SysRegWrite32_17f454fbcdf975ae (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (pure (BPIALLIS ()))))
      else
        (if ((__PSTATE_EL == EL2) : Bool)
        then (pure (BPIALLIS ()))
        else
          (if ((__PSTATE_EL == EL3) : Bool)
          then (pure (BPIALLIS ()))
          else (pure ()))))

/-- Type quantifiers: t : Int -/
def BPIALL_SysRegWrite32_4a4889731f53da78 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_FB ← (( do (pure (_get_HCR_Type_FB (← (HCR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HCR_FB == 1#1)) : Bool)
                  then (pure (BPIALLIS ()))
                  else (pure (BPIALL ())))))
      else
        (if ((__PSTATE_EL == EL2) : Bool)
        then (pure (BPIALL ()))
        else
          (if ((__PSTATE_EL == EL3) : Bool)
          then (pure (BPIALL ()))
          else (pure ()))))

/-- Type quantifiers: t : Int -/
def BPIMVA_SysRegWrite32_913ce21249c53f0d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (pure (BPIMVA (← (R_read t))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (pure (BPIMVA (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (BPIMVA (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CFPRCTX_SysRegWrite32_5c2c25bf2b1d12d6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_EnRCTX ← (( do (pure (_get_SCTLR_EL1_Type_EnRCTX (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EnRCTX ← (( do (pure (_get_SCTLR_Type_EnRCTX (← (SCTLR_read__2 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_CFPRCTX ← (( do (pure (_get_HFGITR_EL2_Type_CFPRCTX (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_EnRCTX ← (( do (pure (_get_SCTLR_EL2_Type_EnRCTX (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__SCTLR_EL1_EnRCTX == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__SCTLR_EnRCTX == 0#1)) : Bool)
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
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_CFPRCTX == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_EnRCTX == 0#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else (AArch32_RestrictPrediction (← (R_read t)) RestrictType_ControlFlow)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_NV == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch32_RestrictPrediction (← (R_read t)) RestrictType_ControlFlow))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_RestrictPrediction (← (R_read t)) RestrictType_ControlFlow)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_RestrictPrediction (← (R_read t)) RestrictType_ControlFlow)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTFRQ_SysRegWrite32_bb1fcec10c61c758 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((IsHighestEL (← readReg PSTATE).EL) : Bool)
  then (CNTFRQ_write (← (R_read t)))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def CNTHCTL_SysRegWrite32_7d97fc0c6abe59e3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (CNTHCTL_write (Mk_CNTHCTL_Type (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (CNTHCTL_write (Mk_CNTHCTL_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHPS_CTL_SysRegWrite32_420a204f985af014 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              then (__set_CNTHPS_CTL_EL2 (Mk_CNTHPS_CTL_EL2_Type (Sail.BitVec.zeroExtend (← (R_read t)) 64)))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                                  then (__set_CNTHP_CTL_EL2 (Mk_CNTHP_CTL_EL2_Type (Sail.BitVec.zeroExtend (← (R_read t)) 64)))
                                  else (__set_CNTP_CTL (Mk_CNTP_CTL_Type (← (R_read t))))))))))))
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
                      then (__set_CNTP_CTL_NS (Mk_CNTP_CTL_Type (← (R_read t))))
                      else (__set_CNTP_CTL (Mk_CNTP_CTL_Type (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (__set_CNTP_CTL_NS (Mk_CNTP_CTL_Type (← (R_read t))))
              else (__set_CNTP_CTL (Mk_CNTP_CTL_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (__set_CNTP_CTL_S (Mk_CNTP_CTL_Type (← (R_read t))))
                  else (__set_CNTP_CTL_NS (Mk_CNTP_CTL_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_CTL_SysRegWrite32_ed680b861de2ac5b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (__set_CNTHP_CTL (Mk_CNTHP_CTL_Type (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (__set_CNTHP_CTL (Mk_CNTHP_CTL_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_SysRegWrite32_1a9db618df39c059 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (CNTHP_CVAL_write (Mk_CNTHP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (CNTHP_CVAL_write (Mk_CNTHP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_SysRegWrite32_8e96a3fad1864250 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let __SCR_EL3_ECVEn ← (( do (pure (_get_SCR_EL3_Type_ECVEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_ECV ← (( do (pure (_get_CNTHCTL_EL2_Type_ECV (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
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
                              then writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                                  then writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))
                                  else
                                    (do
                                      if ((←((pure (((←((IsFeatureImplemented FEAT_ECV) <&&> (do (EL2Enabled ())) <&&> (do (pure (! (← (ELUsingAArch32 EL2))))))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1))) <&&> (do
                                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) : Bool)
                                      then (CNTP_CVAL_write (Mk_CNTP_CVAL_Type (((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTPOFF_EL2))))
                                      else
                                        (do
                                          if ((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) : Bool)
                                          then
                                            (do
                                              if ((__SCR_NS == 1#1) : Bool)
                                              then (CNTP_CVAL_NS_write (Mk_CNTP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ())))))
                                              else writeReg CNTP_CVAL_S (Mk_CNTP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ())))))
                                          else (CNTP_CVAL_write (Mk_CNTP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ())))))))))))))))
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
                      then (CNTP_CVAL_write (Mk_CNTP_CVAL_Type (((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTPOFF_EL2))))
                      else
                        (do
                          if ((←((pure (HaveEL EL3)) <&&> (do
                               (ELUsingAArch32 EL3)))) : Bool)
                          then (CNTP_CVAL_NS_write (Mk_CNTP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ())))))
                          else (CNTP_CVAL_write (Mk_CNTP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (CNTP_CVAL_NS_write (Mk_CNTP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ())))))
              else (CNTP_CVAL_write (Mk_CNTP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg CNTP_CVAL_S (Mk_CNTP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))
                  else (CNTP_CVAL_NS_write (Mk_CNTP_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHVS_CTL_SysRegWrite32_018e2cf152f109f9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then (__set_CNTHVS_CTL_EL2 (Mk_CNTHVS_CTL_EL2_Type (Sail.BitVec.zeroExtend (← (R_read t)) 64)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then (__set_CNTHV_CTL_EL2 (Mk_CNTHV_CTL_EL2_Type (Sail.BitVec.zeroExtend (← (R_read t)) 64)))
                          else (__set_CNTV_CTL (Mk_CNTV_CTL_Type (← (R_read t))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else (__set_CNTV_CTL (Mk_CNTV_CTL_Type (← (R_read t)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (__set_CNTV_CTL (Mk_CNTV_CTL_Type (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_CNTV_CTL (Mk_CNTV_CTL_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTKCTL_SysRegWrite32_e68a84be701ace4f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (CNTKCTL_write (Mk_CNTKCTL_Type (← (R_read t))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (CNTKCTL_write (Mk_CNTKCTL_Type (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (CNTKCTL_write (Mk_CNTKCTL_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTV_TVAL_SysRegWrite32_903e727583f63e89 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      then writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))
                          else
                            (do
                              if ((←((pure (HaveEL EL2)) <&&> (do
                                   (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
                              then (CNTV_CVAL_write (Mk_CNTV_CVAL_Type (((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTVOFF_EL2))))
                              else
                                (do
                                  if ((←((pure (HaveEL EL2)) <&&> (do
                                       (ELUsingAArch32 EL2)))) : Bool)
                                  then (CNTV_CVAL_write (Mk_CNTV_CVAL_Type (((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))) - (← (CNTVOFF_read ())))))
                                  else (CNTV_CVAL_write (Mk_CNTV_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ())))))))))))))
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
              if ((←((pure (HaveEL EL2)) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
              then (CNTV_CVAL_write (Mk_CNTV_CVAL_Type (((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))) - (← readReg CNTVOFF_EL2))))
              else
                (do
                  if ((←((pure (HaveEL EL2)) <&&> (do
                       (ELUsingAArch32 EL2)))) : Bool)
                  then (CNTV_CVAL_write (Mk_CNTV_CVAL_Type (((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))) - (← (CNTVOFF_read ())))))
                  else (CNTV_CVAL_write (Mk_CNTV_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (CNTV_CVAL_write (Mk_CNTV_CVAL_Type (((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))) - (← (CNTVOFF_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((HaveEL EL2) : Bool)
                  then (CNTV_CVAL_write (Mk_CNTV_CVAL_Type (((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))) - (← (CNTVOFF_read ())))))
                  else (CNTV_CVAL_write (Mk_CNTV_CVAL_Type ((sign_extend (← (R_read t)) 64) + (← (PhysicalCountInt ()))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CONTEXTIDR_SysRegWrite32_3295051c92606610 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                          then (CONTEXTIDR_NS_write (Mk_CONTEXTIDR_Type (← (R_read t))))
                          else (CONTEXTIDR_write (Mk_CONTEXTIDR_Type (← (R_read t)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (CONTEXTIDR_NS_write (Mk_CONTEXTIDR_Type (← (R_read t))))
              else (CONTEXTIDR_write (Mk_CONTEXTIDR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg CONTEXTIDR_S (Mk_CONTEXTIDR_Type (← (R_read t)))
                  else (CONTEXTIDR_NS_write (Mk_CONTEXTIDR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def COSPRCTX_SysRegWrite32_4f4dd157b3f4905c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_EnRCTX ← (( do (pure (_get_SCTLR_EL1_Type_EnRCTX (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EnRCTX ← (( do (pure (_get_SCTLR_Type_EnRCTX (← (SCTLR_read__2 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_COSPRCTX ← (( do (pure (_get_HFGITR_EL2_Type_COSPRCTX (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_EnRCTX ← (( do (pure (_get_SCTLR_EL2_Type_EnRCTX (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__SCTLR_EL1_EnRCTX == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__SCTLR_EnRCTX == 0#1)) : Bool)
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
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_COSPRCTX == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_EnRCTX == 0#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else (AArch32_RestrictPrediction (← (R_read t)) RestrictType_Other)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_NV == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch32_RestrictPrediction (← (R_read t)) RestrictType_Other))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_RestrictPrediction (← (R_read t)) RestrictType_Other)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_RestrictPrediction (← (R_read t)) RestrictType_Other)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CP15DMB_SysRegWrite32_d17f32fecbb5fdad (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_CP15BEN ← (( do (pure (_get_SCTLR_EL1_Type_CP15BEN (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_CP15BEN ← (( do (pure (_get_SCTLR_EL2_Type_CP15BEN (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_CP15BEN ← (( do (pure (_get_SCTLR_Type_CP15BEN (← (SCTLR_read__2 ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HSCTLR_CP15BEN ← (( do (pure (_get_HSCTLR_Type_CP15BEN (← (HSCTLR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__SCTLR_EL1_CP15BEN == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_CP15BEN == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__SCTLR_CP15BEN == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else (pure (CP15DMB ())))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (pure (CP15DMB ())))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HSCTLR_CP15BEN == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure (CP15DMB ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (pure (CP15DMB ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CP15DSB_SysRegWrite32_e8d50e04da138ecc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_CP15BEN ← (( do (pure (_get_SCTLR_EL1_Type_CP15BEN (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_CP15BEN ← (( do (pure (_get_SCTLR_EL2_Type_CP15BEN (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_CP15BEN ← (( do (pure (_get_SCTLR_Type_CP15BEN (← (SCTLR_read__2 ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HSCTLR_CP15BEN ← (( do (pure (_get_HSCTLR_Type_CP15BEN (← (HSCTLR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__SCTLR_EL1_CP15BEN == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_CP15BEN == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__SCTLR_CP15BEN == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else (pure (CP15DSB ())))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (pure (CP15DSB ())))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HSCTLR_CP15BEN == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure (CP15DSB ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (pure (CP15DSB ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CP15ISB_SysRegWrite32_b2e3d8ab360938e2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_CP15BEN ← (( do (pure (_get_SCTLR_EL1_Type_CP15BEN (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_CP15BEN ← (( do (pure (_get_SCTLR_EL2_Type_CP15BEN (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_CP15BEN ← (( do (pure (_get_SCTLR_Type_CP15BEN (← (SCTLR_read__2 ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HSCTLR_CP15BEN ← (( do (pure (_get_HSCTLR_Type_CP15BEN (← (HSCTLR_read ())))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__SCTLR_EL1_CP15BEN == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_CP15BEN == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__SCTLR_CP15BEN == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else (pure (CP15ISB ())))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (pure (CP15ISB ())))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HSCTLR_CP15BEN == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure (CP15ISB ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (pure (CP15ISB ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPACR_SysRegWrite32_512a962d4019b387 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              else (__set_CPACR (Mk_CPACR_Type (← (R_read t))))))))))
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
                  else (__set_CPACR (Mk_CPACR_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_CPACR (Mk_CPACR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPPRCTX_SysRegWrite32_07d924e6f4753edc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_EnRCTX ← (( do (pure (_get_SCTLR_EL1_Type_EnRCTX (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EnRCTX ← (( do (pure (_get_SCTLR_Type_EnRCTX (← (SCTLR_read__2 ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGITR_EL2_CPPRCTX ← (( do (pure (_get_HFGITR_EL2_Type_CPPRCTX (← readReg HFGITR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_EnRCTX ← (( do (pure (_get_SCTLR_EL2_Type_EnRCTX (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
             (pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))))))) && (__SCTLR_EL1_EnRCTX == 0#1)) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8)))
      else
        (do
          if (((← (ELUsingAArch32 EL1)) && (__SCTLR_EnRCTX == 0#1)) : Bool)
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
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGITR_EL2_CPPRCTX == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_EnRCTX == 0#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else (AArch32_RestrictPrediction (← (R_read t)) RestrictType_CachePrefetch)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T7 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T7 == 1#1)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_NV == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else (AArch32_RestrictPrediction (← (R_read t)) RestrictType_CachePrefetch))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_RestrictPrediction (← (R_read t)) RestrictType_CachePrefetch)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_RestrictPrediction (← (R_read t)) RestrictType_CachePrefetch)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CSSELR_SysRegWrite32_707b283268d02f0f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                  then (CSSELR_NS_write (Mk_CSSELR_Type (← (R_read t))))
                                  else (CSSELR_write (Mk_CSSELR_Type (← (R_read t)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (CSSELR_NS_write (Mk_CSSELR_Type (← (R_read t))))
              else (CSSELR_write (Mk_CSSELR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg CSSELR_S (Mk_CSSELR_Type (← (R_read t)))
                  else (CSSELR_NS_write (Mk_CSSELR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DACR_SysRegWrite32_bfabed8f69d486b5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T3 ← (( do (pure (_get_HSTR_EL2_Type_T3 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T3 ← (( do (pure (_get_HSTR_Type_T3 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                          then (DACR_NS_write (Mk_DACR_Type (← (R_read t))))
                          else (DACR_write (Mk_DACR_Type (← (R_read t)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (DACR_NS_write (Mk_DACR_Type (← (R_read t))))
              else (DACR_write (Mk_DACR_Type (← (R_read t)))))
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
                          then writeReg DACR_S (Mk_DACR_Type (← (R_read t)))
                          else (DACR_NS_write (Mk_DACR_Type (← (R_read t)))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegWrite32_08e08cceb84c7c71 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              else (DBGBCR_set 8 (Mk_DBGBCR_Type (← (R_read t)))))))))
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
                          else (DBGBCR_set 8 (Mk_DBGBCR_Type (← (R_read t)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (DBGBCR_set 8 (Mk_DBGBCR_Type (← (R_read t)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegWrite32_122d009e13ded976 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              else (DBGBCR_set 1 (Mk_DBGBCR_Type (← (R_read t)))))))))
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
                          else (DBGBCR_set 1 (Mk_DBGBCR_Type (← (R_read t)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (DBGBCR_set 1 (Mk_DBGBCR_Type (← (R_read t)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegWrite32_28709afae2cd2b96 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              else (DBGBCR_set 15 (Mk_DBGBCR_Type (← (R_read t)))))))))
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
                          else (DBGBCR_set 15 (Mk_DBGBCR_Type (← (R_read t)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (DBGBCR_set 15 (Mk_DBGBCR_Type (← (R_read t)))))
                  else (pure ())))))


