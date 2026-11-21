import Armv9.Flow
import Armv9.Prelude
import Armv9.V8Base
import Armv9.Stubs
import Armv9.SysregsAutogen.P04
import Armv9.SysregsAutogen.P07
import Armv9.SysregsAutogen.P08
import Armv9.SysregsAutogen.P11
import Armv9.SysregsAutogen.P14
import Armv9.SysregsAutogen.P15

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
def SPMOVSCLR_EL0_SysRegWrite_631efaee847d8a50 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMOVS ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMOVS (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
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
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) != 0b11#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMOVS == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) != 0b11#2))))) : Bool)
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
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (pure (SPMOVSCLR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))))
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
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMOVS == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) != 0b11#2))))) : Bool)
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
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (pure (SPMOVSCLR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))
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
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
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
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (pure (SPMOVSCLR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMOVSCLR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMOVSSET_EL0_SysRegWrite_2a7560d8e9955a98 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMOVS ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMOVS (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
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
                       (pure ((← (__get_selected_SPMACCESSR_EL1_field ())) != 0b11#2))))) : Bool)
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMOVS == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) != 0b11#2))))) : Bool)
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
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (pure (SPMOVSSET_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))))
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
                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMOVS == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) != 0b11#2))))) : Bool)
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
                                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                      else (pure (SPMOVSSET_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))
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
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
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
                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else (pure (SPMOVSSET_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMOVSSET_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMROOTCR_EL3_SysRegWrite_0baeba57352c9f52 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (pure (SPMROOTCR_EL3_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMSCR_EL1_SysRegWrite_ad1ae69a7d554d65 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMSCR_EL1 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMSCR_EL1 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_EnSPM ← (( do (pure (_get_MDCR_EL2_Type_EnSPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  if ((←((IsCurrentSecurityState SS_NonSecure) <||> (do
       (IsFeatureImplemented FEAT_RME) <&&> (do
         (IsCurrentSecurityState SS_Realm))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((((←((EL2Enabled ()) <&&> (do
                               (IsFeatureImplemented FEAT_FGT2)))) && (HaveEL EL3)) && (__SCR_EL3_FGTEn2 == 0#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMSCR_EL1 == 0#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                          else
                            (do
                              if (((← (EL2Enabled ())) && (__MDCR_EL2_EnSPM == 0#1)) : Bool)
                              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                              else
                                (do
                                  if ((←((EL2Enabled ()) <&&> (do
                                       (pure ((← (__get_selected_SPMACCESSR_EL2_field ())) != 0b11#2))))) : Bool)
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
                                               (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                                          else (pure (SPMSCR_EL1_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))
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
                           (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
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
                                   (pure ((← (__get_selected_SPMACCESSR_EL3_field ())) != 0b11#2))))) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                              else (pure (SPMSCR_EL1_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (pure (SPMSCR_EL1_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def AArch64_AutoGen_SysInstrWithResult (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((((((CRm == 0b0111#4) && (CRn == 0b0111#4)) && (op0 == 0b01#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
  then (do (GCSSS2_SysInstrWithResult_f9ffdfaa333b34bf el op0 op1 CRn op2 CRm t))
  else
    (do
      if ((((((CRm == 0b0111#4) && (CRn == 0b0111#4)) && (op0 == 0b01#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
      then (do (GCSPOPM_SysInstrWithResult_785f34ad5cd557fe el op0 op1 CRn op2 CRm t))
      else (AArch64_UnallocatedSysRegAccess op0 op1 CRn op2 CRm false t))

/-- Type quantifiers: t : Int, t2 : Int -/
def AArch32_AutoGen_SysRegWrite64 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((CRm == 0b1100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
  then (do (ICC_SGI1R_SysRegWrite64_e5d73969c7266f22 el coproc opc1 CRm t t2))
  else
    (do
      if ((((CRm == 0b1100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
      then (do (ICC_SGI0R_SysRegWrite64_3055f033253258da el coproc opc1 CRm t t2))
      else
        (do
          if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
          then (do (CNTVOFF_SysRegWrite64_772809c07f941c73 el coproc opc1 CRm t t2))
          else
            (do
              if ((((CRm == 0b1100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
              then (do (ICC_ASGI1R_SysRegWrite64_29140bc551f7529b el coproc opc1 CRm t t2))
              else
                (do
                  if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                  then (do (CNTHV_CVAL_SysRegWrite64_e72c3c45ec57bc51 el coproc opc1 CRm t t2))
                  else
                    (do
                      if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                      then (do (CNTHPS_CVAL_SysRegWrite64_34fa93164860ce59 el coproc opc1 CRm t t2))
                      else
                        (do
                          if ((((CRm == 0b0111#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                          then (do (PAR_SysRegWrite64_867d7cbf8d644296 el coproc opc1 CRm t t2))
                          else
                            (do
                              if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                              then (do (CNTHP_CVAL_SysRegWrite64_558ce8493f8ab75e el coproc opc1 CRm t t2))
                              else
                                (do
                                  if ((((CRm == 0b1001#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                  then (do (PMCCNTR_SysRegWrite64_51a4ab1690d771a1 el coproc opc1 CRm t t2))
                                  else
                                    (do
                                      if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                      then (do (TTBR1_SysRegWrite64_7d88e184b6073f76 el coproc opc1 CRm t t2))
                                      else
                                        (do
                                          if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                          then (do (HTTBR_SysRegWrite64_3e34efab7aaa3ec6 el coproc opc1 CRm t t2))
                                          else
                                            (do
                                              if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                              then (do (TTBR0_SysRegWrite64_c1a707eccbf8dd96 el coproc opc1 CRm t t2))
                                              else
                                                (do
                                                  if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                  then (do (VTTBR_SysRegWrite64_ab86e13c6c48344f el coproc opc1 CRm t t2))
                                                  else
                                                    (do
                                                      if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                      then (do (AMEVCNTR0_SysRegWrite64_125e5d1a241e0a34 el coproc opc1 CRm t t2))
                                                      else
                                                        (do
                                                          if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                          then (do (AMEVCNTR0_SysRegWrite64_a509b10e64184e5e el coproc opc1 CRm t t2))
                                                          else
                                                            (do
                                                              if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                              then (do (AMEVCNTR0_SysRegWrite64_ffac5e218d5b074d el coproc opc1 CRm t t2))
                                                              else
                                                                (do
                                                                  if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                  then (do (AMEVCNTR0_SysRegWrite64_00363288e0ffc481 el coproc opc1 CRm t t2))
                                                                  else
                                                                    (do
                                                                      if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0111#4)) : Bool)
                                                                      then (do (AMEVCNTR1_SysRegWrite64_469c861805be726d el coproc opc1 CRm t t2))
                                                                      else
                                                                        (do
                                                                          if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                                          then (do (AMEVCNTR1_SysRegWrite64_caa18a28b827223b el coproc opc1 CRm t t2))
                                                                          else
                                                                            (do
                                                                              if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0101#4)) : Bool)
                                                                              then (do (AMEVCNTR1_SysRegWrite64_6aa1c0a95da044bc el coproc opc1 CRm t t2))
                                                                              else
                                                                                (do
                                                                                  if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                                                                  then (do (AMEVCNTR1_SysRegWrite64_3cf44094d12f6f9a el coproc opc1 CRm t t2))
                                                                                  else
                                                                                    (do
                                                                                      if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                                                      then (do (AMEVCNTR1_SysRegWrite64_8df7cb996ace4301 el coproc opc1 CRm t t2))
                                                                                      else
                                                                                        (do
                                                                                          if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                                                          then (do (AMEVCNTR1_SysRegWrite64_1415f513493b61c8 el coproc opc1 CRm t t2))
                                                                                          else
                                                                                            (do
                                                                                              if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                                                              then (do (AMEVCNTR1_SysRegWrite64_ec5133758c2bd694 el coproc opc1 CRm t t2))
                                                                                              else
                                                                                                (do
                                                                                                  if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                                                  then (do (AMEVCNTR1_SysRegWrite64_683d5eccd985c418 el coproc opc1 CRm t t2))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0111#4)) : Bool)
                                                                                                      then (do (AMEVCNTR1_SysRegWrite64_a0a98205a8cc86f4 el coproc opc1 CRm t t2))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                                                                          then (do (AMEVCNTR1_SysRegWrite64_8ea485840df13e8b el coproc opc1 CRm t t2))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0101#4)) : Bool)
                                                                                                              then (do (AMEVCNTR1_SysRegWrite64_9589f0d5bbc35480 el coproc opc1 CRm t t2))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                                                                                                  then (do (AMEVCNTR1_SysRegWrite64_18488936f5130285 el coproc opc1 CRm t t2))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                                                                                      then (do (AMEVCNTR1_SysRegWrite64_80489a0c42f5990f el coproc opc1 CRm t t2))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                                                                                          then (do (AMEVCNTR1_SysRegWrite64_4a0c18bf00eccda4 el coproc opc1 CRm t t2))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                                                                                              then (do (AMEVCNTR1_SysRegWrite64_06329c412b3ab5ff el coproc opc1 CRm t t2))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                                                                                  then (do (AMEVCNTR1_SysRegWrite64_8a065d943b8f719e el coproc opc1 CRm t t2))
                                                                                                                                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))))))))))))))))))))))))))))))))

/-- Type quantifiers: k_read : Bool, t : Int -/
def AArch32_UnallocatedSysRegAccess (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (read : Bool) (t : Int) : SailM Unit := SailME.run do
  let tid3_trap : Bool := false
  let tid3_trap ← (( do
    if ((←((pure ((BEq.beq (← (PLOfEL (← readReg PSTATE).EL)) PL1) && read)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure ((_get_HCR_EL2_Type_TID3 (← readReg HCR_EL2)) == 1#1))))) : Bool)
    then
      (do
        if ((← (HaveFGTExt ())) : Bool)
        then (pure true)
        else (__IMPDEF_boolean "Unallocated encodings trapped by HCR_EL2.TID3"))
    else (pure tid3_trap) ) : SailME Unit Bool )
  if (((((tid3_trap && (((BitVec.toNat coproc) == 15) : Bool)) && (((BitVec.toNat opc1) == 0) : Bool)) && (((BitVec.toNat CRn) == 0) : Bool)) && ((((BitVec.toNat CRm) == 2) || ((((BitVec.toNat CRm) == 3) || ((((BitVec.toNat CRm) == 4) || ((((BitVec.toNat CRm) == 5) || ((((BitVec.toNat CRm) == 6) || (((BitVec.toNat CRm) == 7) : Bool)) : Bool)) : Bool)) : Bool)) : Bool)) : Bool)) : Bool)
  then
    (do
      if ((← (ELUsingAArch32 EL2)) : Bool)
      then (AArch32_SystemAccessTrap M32_Hyp (BitVec.toNat 0x3#4))
      else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x3#4)))
  else (pure ())
  (AArch32_CheckCP15InstrCoarseTraps (BitVec.toNat CRn) (← (GetNreg ())) (BitVec.toNat CRm))
  if (((((((BitVec.toNat coproc) == 15) && (opc1 == 0b000#3)) && (CRn == 0b0000#4)) && (CRm == 0b0010#4)) && (opc2 == 0b111#3)) : Bool)
  then
    (do
      if ((((← readReg PSTATE).EL != EL0) && read) : Bool)
      then SailME.throw (← (do (R_set t (← (__UNKNOWN_bits 32)))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else (pure ())
  if ((((((BitVec.toNat coproc) == 15) && (opc1 == 0b000#3)) && (CRn == 0b0000#4)) && (((BitVec.toNat CRm) ≥b 3) : Bool)) : Bool)
  then
    (do
      if ((((← readReg PSTATE).EL != EL0) && read) : Bool)
      then SailME.throw (← (do (R_set t (← (__UNKNOWN_bits 32)))))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else (pure ())
  if ((! read) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((BitVec.toNat coproc) == 15) && (CRn == 0b0000#4)) : Bool)
  then
    (do
      if (((BitVec.toNat opc1) >b 0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        SailME.throw (← (do
            if (((CRm == 0b0011#4) && ((opc2 == 0b000#3) || ((opc2 == 0b001#3) || (opc2 == 0b010#3)))) : Bool)
            then (do (R_set t (← (__UNKNOWN_bits 32))))
            else
              (do
                if ((((CRm == 0b0100#4) || ((CRm == 0b0110#4) || (CRm == 0b0111#4))) && ((opc2 == 0b000#3) || ((opc2 == 0b001#3) || (opc2 == 0b111#3)))) : Bool)
                then (do (R_set t (← (__UNKNOWN_bits 32))))
                else
                  (do
                    if (((CRm == 0b0101#4) && ((opc2 == 0b000#3) || ((opc2 == 0b001#3) || ((opc2 == 0b100#3) || (opc2 == 0b101#3))))) : Bool)
                    then (do (R_set t (← (__UNKNOWN_bits 32))))
                    else (do (R_set t (Zeros (n := 32)))))))))
  else (pure ())
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int, t2 : Int -/
def AArch32_AutoGen_SysRegRead64 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((CRm == 0b0010#4) && (coproc == 0b1110#4)) && (opc1 == 0b0000#4)) : Bool)
  then (do (DBGDSAR_SysRegRead64_2f971e6eb001648b el coproc opc1 CRm t t2))
  else
    (do
      if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
      then (do (CNTVOFF_SysRegRead64_66c4d48806fce48e el coproc opc1 CRm t t2))
      else
        (do
          if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
          then (do (CNTHV_CVAL_SysRegRead64_7bf312f271feb72e el coproc opc1 CRm t t2))
          else
            (do
              if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
              then (do (CNTHPS_CVAL_SysRegRead64_aa5fa6170d1a3db5 el coproc opc1 CRm t t2))
              else
                (do
                  if ((((CRm == 0b0111#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                  then (do (PAR_SysRegRead64_bd143a1fe560ae4b el coproc opc1 CRm t t2))
                  else
                    (do
                      if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                      then (do (CNTPCT_SysRegRead64_7dc4fea5bbad7fe9 el coproc opc1 CRm t t2))
                      else
                        (do
                          if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                          then (do (CNTHP_CVAL_SysRegRead64_bedb5ea1dc82962f el coproc opc1 CRm t t2))
                          else
                            (do
                              if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b1000#4)) : Bool)
                              then (do (CNTPCT_SysRegRead64_7dc4fea5bbad7fe9 el coproc opc1 CRm t t2))
                              else
                                (do
                                  if ((((CRm == 0b1001#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                  then (do (PMCCNTR_SysRegRead64_1cf48d19bc879bd3 el coproc opc1 CRm t t2))
                                  else
                                    (do
                                      if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                      then (do (CNTVCT_SysRegRead64_6e373436952b9ca9 el coproc opc1 CRm t t2))
                                      else
                                        (do
                                          if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b1001#4)) : Bool)
                                          then (do (CNTVCT_SysRegRead64_6e373436952b9ca9 el coproc opc1 CRm t t2))
                                          else
                                            (do
                                              if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                              then (do (TTBR1_SysRegRead64_6988488afc2dce1a el coproc opc1 CRm t t2))
                                              else
                                                (do
                                                  if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                                  then (do (HTTBR_SysRegRead64_5b679aebf4474d8a el coproc opc1 CRm t t2))
                                                  else
                                                    (do
                                                      if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                      then (do (TTBR0_SysRegRead64_9396816aa24cfa90 el coproc opc1 CRm t t2))
                                                      else
                                                        (do
                                                          if ((((CRm == 0b0001#4) && (coproc == 0b1110#4)) && (opc1 == 0b0000#4)) : Bool)
                                                          then (do (DBGDRAR_SysRegRead64_89f87ddb7d53b509 el coproc opc1 CRm t t2))
                                                          else
                                                            (do
                                                              if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                              then (do (VTTBR_SysRegRead64_aec948eb11ac7d09 el coproc opc1 CRm t t2))
                                                              else
                                                                (do
                                                                  if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                                  then (do (AMEVCNTR0_SysRegRead64_58cd2445e81e8975 el coproc opc1 CRm t t2))
                                                                  else
                                                                    (do
                                                                      if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                                      then (do (AMEVCNTR0_SysRegRead64_bf8f308b8b559115 el coproc opc1 CRm t t2))
                                                                      else
                                                                        (do
                                                                          if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                                          then (do (AMEVCNTR0_SysRegRead64_66e81afe82d2c192 el coproc opc1 CRm t t2))
                                                                          else
                                                                            (do
                                                                              if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                              then (do (AMEVCNTR0_SysRegRead64_2b274c768298c3f9 el coproc opc1 CRm t t2))
                                                                              else
                                                                                (do
                                                                                  if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0111#4)) : Bool)
                                                                                  then (do (AMEVCNTR1_SysRegRead64_51a9ce69caa26d97 el coproc opc1 CRm t t2))
                                                                                  else
                                                                                    (do
                                                                                      if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                                                      then (do (AMEVCNTR1_SysRegRead64_cdf416f7d354cbf5 el coproc opc1 CRm t t2))
                                                                                      else
                                                                                        (do
                                                                                          if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0101#4)) : Bool)
                                                                                          then (do (AMEVCNTR1_SysRegRead64_065fe37bc5a680bd el coproc opc1 CRm t t2))
                                                                                          else
                                                                                            (do
                                                                                              if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                                                                              then (do (AMEVCNTR1_SysRegRead64_d4ffe491a2456c2b el coproc opc1 CRm t t2))
                                                                                              else
                                                                                                (do
                                                                                                  if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                                                                  then (do (AMEVCNTR1_SysRegRead64_839ed88b8f796549 el coproc opc1 CRm t t2))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                                                                      then (do (AMEVCNTR1_SysRegRead64_fa3226080978524b el coproc opc1 CRm t t2))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                                                                          then (do (AMEVCNTR1_SysRegRead64_4cd25036d674f8ac el coproc opc1 CRm t t2))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                                                              then (do (AMEVCNTR1_SysRegRead64_9c104b95f67d3b22 el coproc opc1 CRm t t2))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0111#4)) : Bool)
                                                                                                                  then (do (AMEVCNTR1_SysRegRead64_141e5d18f9a75c13 el coproc opc1 CRm t t2))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                                                                                      then (do (AMEVCNTR1_SysRegRead64_6f64074808614759 el coproc opc1 CRm t t2))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0101#4)) : Bool)
                                                                                                                          then (do (AMEVCNTR1_SysRegRead64_2d5e01434567b282 el coproc opc1 CRm t t2))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                                                                                                              then (do (AMEVCNTR1_SysRegRead64_eefece484f7466c9 el coproc opc1 CRm t t2))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                                                                                                  then (do (AMEVCNTR1_SysRegRead64_4e22e3365cdbab7d el coproc opc1 CRm t t2))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                                                                                                      then (do (AMEVCNTR1_SysRegRead64_13f84beb778d3114 el coproc opc1 CRm t t2))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                                                                                                          then (do (AMEVCNTR1_SysRegRead64_132f33bfb64bea99 el coproc opc1 CRm t t2))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                                                                                              then (do (AMEVCNTR1_SysRegRead64_a118420696d1228f el coproc opc1 CRm t t2))
                                                                                                                                              else (sailThrow ((Error_Undefined ())) : SailM Unit))))))))))))))))))))))))))))))))))))

def AArch32_STC (coproc : (BitVec 4)) (CRd : (BitVec 4)) (address : (BitVec 32)) : SailM Unit := do
  if (((CRd == 0b0101#4) && (coproc == 0b1110#4)) : Bool)
  then (do (DBGDTRRXint_STC_521dc9133ebece9c coproc CRd address))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

def AArch32_LDC (coproc : (BitVec 4)) (CRd : (BitVec 4)) (address : (BitVec 32)) : SailM Unit := do
  if (((CRd == 0b0101#4) && (coproc == 0b1110#4)) : Bool)
  then (do (DBGDTRTXint_LDC_da4baa792b999a1f coproc CRd address))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int, t2 : Int -/
def S3_op1_Cn_Cm_op2_SysRegRead128_6403c05d5d1898d5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EnIDCP128 ← (( do (pure (_get_SCR_EL3_Type_EnIDCP128 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCTLR_EL1_TIDCP ← (( do (pure (_get_SCTLR_EL1_Type_TIDCP (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_TIDCP ← (( do (pure (_get_SCTLR_EL2_Type_TIDCP (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR2_EL1_EnIDCP128 ← (( do (pure (_get_SCTLR2_EL1_Type_EnIDCP128 (← readReg SCTLR2_EL1))) ) : SailM (BitVec 1) )
  let __SCTLR2_EL2_EnIDCP128 ← (( do (pure (_get_SCTLR2_EL2_Type_EnIDCP128 (← readReg SCTLR2_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_EnIDCP128 ← (( do (pure (_get_HCRX_EL2_Type_EnIDCP128 (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TIDCP ← (( do (pure (_get_HCR_EL2_Type_TIDCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_TIDCP == 1#1)) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x14#8)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_TIDCP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((! (← (IsSCTLR2EL1Enabled ()))) || (__SCTLR2_EL1_EnIDCP128 == 0#1)))))) : Bool)
                  then
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((! (← (IsSCTLR2EL2Enabled ()))) || (__SCTLR2_EL2_EnIDCP128 == 0#1)))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_EnIDCP128 == 0#1)))))) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                              else (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TIDCP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_EnIDCP128 == 0#1)))))) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def S3_op1_Cn_Cm_op2_SysRegWrite128_54572e14feed5fe8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EnIDCP128 ← (( do (pure (_get_SCR_EL3_Type_EnIDCP128 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCTLR_EL1_TIDCP ← (( do (pure (_get_SCTLR_EL1_Type_TIDCP (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_TIDCP ← (( do (pure (_get_SCTLR_EL2_Type_TIDCP (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR2_EL1_EnIDCP128 ← (( do (pure (_get_SCTLR2_EL1_Type_EnIDCP128 (← readReg SCTLR2_EL1))) ) : SailM (BitVec 1) )
  let __SCTLR2_EL2_EnIDCP128 ← (( do (pure (_get_SCTLR2_EL2_Type_EnIDCP128 (← readReg SCTLR2_EL2))) ) : SailM (BitVec 1) )
  let __HCRX_EL2_EnIDCP128 ← (( do (pure (_get_HCRX_EL2_Type_EnIDCP128 (← readReg HCRX_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TIDCP ← (( do (pure (_get_HCR_EL2_Type_TIDCP (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((! (←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_TIDCP == 1#1)) : Bool)
          then
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x14#8)))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_TIDCP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
                       (pure ((! (← (IsSCTLR2EL1Enabled ()))) || (__SCTLR2_EL1_EnIDCP128 == 0#1)))))) : Bool)
                  then
                    (do
                      if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((! (← (IsSCTLR2EL2Enabled ()))) || (__SCTLR2_EL2_EnIDCP128 == 0#1)))))) : Bool)
                      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                               (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_EnIDCP128 == 0#1)))))) : Bool)
                          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                          else
                            (do
                              if (((HaveEL EL3) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
                              then
                                (do
                                  if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                              else (AArch64_ImpDefSysRegWrite128 op0 op1 CRn CRm op2 t (t +i 1)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TIDCP == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure ((! (← (IsHCRXEL2Enabled ()))) || (__HCRX_EL2_EnIDCP128 == 0#1)))))) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                      else (AArch64_ImpDefSysRegWrite128 op0 op1 CRn CRm op2 t (t +i 1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_EnIDCP128 == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8)))
                  else (AArch64_ImpDefSysRegWrite128 op0 op1 CRn CRm op2 t (t +i 1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_ImpDefSysRegWrite128 op0 op1 CRn CRm op2 t (t +i 1))
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def S1_op1_Cn_Cm_op2_SysOpsWrite128_8cc8b9dd1f9a8cdc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x14#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_TIDCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (AArch64_ImpDefSysInstr128 1 op1 CRn CRm op2 t t2)))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TIDCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8))
          else (AArch64_ImpDefSysInstr128 1 op1 CRn CRm op2 t t2))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_ImpDefSysInstr128 1 op1 CRn CRm op2 t t2)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_ImpDefSysInstr128 1 op1 CRn CRm op2 t t2)
              else (pure ()))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_AutoGen_SysRegRead128 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((((CRm == 0b0100#4) && (CRn == 0b0111#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
  then (do (PAR_EL1_SysRegRead128_8206ac7c9b0eef57 el op0 op1 CRn op2 CRm t t2))
  else
    (do
      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
      then (do (RCWSMASK_EL1_SysRegRead128_7cac5e35b1fae5f9 el op0 op1 CRn op2 CRm t t2))
      else
        (do
          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
          then (do (TTBR1_EL2_SysRegRead128_ae708511fcb38e92 el op0 op1 CRn op2 CRm t t2))
          else
            (do
              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
              then (do (TTBR1_EL1_SysRegRead128_16388106e031d578 el op0 op1 CRn op2 CRm t t2))
              else
                (do
                  if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                  then (do (TTBR0_EL2_SysRegRead128_05dc18b820cc86b7 el op0 op1 CRn op2 CRm t t2))
                  else
                    (do
                      if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                      then (do (TTBR0_EL1_SysRegRead128_e74a87d5451e7769 el op0 op1 CRn op2 CRm t t2))
                      else
                        (do
                          if ((((((CRm == 0b0001#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                          then (do (VTTBR_EL2_SysRegRead128_a9b3226c12a0e07e el op0 op1 CRn op2 CRm t t2))
                          else
                            (do
                              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                              then (do (TTBR0_EL1_SysRegRead128_ef7a13f49fb9674d el op0 op1 CRn op2 CRm t t2))
                              else
                                (do
                                  if ((((((match (CRm : BitVec 4) with
                                             | b__0 => true : Bool) && (let b__1 := CRn
                                             if ((((Sail.BitVec.extractLsb b__1 3 3) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__1 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                                             then true
                                             else false : Bool)) && (op0 == 0b11#2)) && (match (op1 : BitVec 3) with
                                         | b__2 => true : Bool)) && (match (op2 : BitVec 3) with
                                       | b__3 => true : Bool)) : Bool)
                                  then (do (S3_op1_Cn_Cm_op2_SysRegRead128_6403c05d5d1898d5 el op0 op1 CRn op2 CRm t t2))
                                  else
                                    (do
                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                      then (do (RCWMASK_EL1_SysRegRead128_7c7466f3a5148cfe el op0 op1 CRn op2 CRm t t2))
                                      else
                                        (do
                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                          then (do (TTBR1_EL2_SysRegRead128_712360e50061655a el op0 op1 CRn op2 CRm t t2))
                                          else (AArch64_UnallocatedSysRegAccess op0 op1 CRn op2 CRm true t)))))))))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_AutoGen_SysRegWrite128 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((((CRm == 0b0100#4) && (CRn == 0b0111#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
  then (do (PAR_EL1_SysRegWrite128_e67f3244d494abe6 el op0 op1 CRn op2 CRm t t2))
  else
    (do
      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
      then (do (RCWSMASK_EL1_SysRegWrite128_d70b97b0479af313 el op0 op1 CRn op2 CRm t t2))
      else
        (do
          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
          then (do (TTBR1_EL2_SysRegWrite128_4bfd1913f2c26b7d el op0 op1 CRn op2 CRm t t2))
          else
            (do
              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
              then (do (TTBR1_EL1_SysRegWrite128_d20c29029eb4ed94 el op0 op1 CRn op2 CRm t t2))
              else
                (do
                  if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                  then (do (TTBR0_EL2_SysRegWrite128_db720477dd35bd78 el op0 op1 CRn op2 CRm t t2))
                  else
                    (do
                      if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                      then (do (TTBR0_EL1_SysRegWrite128_66ee61de597f133e el op0 op1 CRn op2 CRm t t2))
                      else
                        (do
                          if ((((((CRm == 0b0001#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                          then (do (VTTBR_EL2_SysRegWrite128_3ec09d9d33270957 el op0 op1 CRn op2 CRm t t2))
                          else
                            (do
                              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                              then (do (TTBR0_EL1_SysRegWrite128_8ea27f288a4b152e el op0 op1 CRn op2 CRm t t2))
                              else
                                (do
                                  if ((((((match (CRm : BitVec 4) with
                                             | b__0 => true : Bool) && (let b__1 := CRn
                                             if ((((Sail.BitVec.extractLsb b__1 3 3) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__1 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                                             then true
                                             else false : Bool)) && (op0 == 0b11#2)) && (match (op1 : BitVec 3) with
                                         | b__2 => true : Bool)) && (match (op2 : BitVec 3) with
                                       | b__3 => true : Bool)) : Bool)
                                  then (do (S3_op1_Cn_Cm_op2_SysRegWrite128_54572e14feed5fe8 el op0 op1 CRn op2 CRm t t2))
                                  else
                                    (do
                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                      then (do (RCWMASK_EL1_SysRegWrite128_b8a59eaf95f35a5f el op0 op1 CRn op2 CRm t t2))
                                      else
                                        (do
                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                          then (do (TTBR1_EL2_SysRegWrite128_c87556637100112b el op0 op1 CRn op2 CRm t t2))
                                          else (AArch64_UnallocatedSysRegAccess op0 op1 CRn op2 CRm false t)))))))))))

/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_AutoGen_SysOpsWrite128 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((((CRm == 0b0010#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
  then (do (TLBIP_RVAE3IS_SysOpsWrite128_46b2dc8d96c6ca59 el op0 op1 CRn op2 CRm t t2))
  else
    (do
      if ((((((CRm == 0b0010#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
      then (do (TLBIP_RVAE3IS_SysOpsWrite128_b118fa02f013962a el op0 op1 CRn op2 CRm t t2))
      else
        (do
          if ((((((CRm == 0b0001#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
          then (do (TLBIP_VAALE1OS_SysOpsWrite128_323a394d866290cd el op0 op1 CRn op2 CRm t t2))
          else
            (do
              if ((((((CRm == 0b0001#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
              then (do (TLBIP_VAALE1OS_SysOpsWrite128_4c241ac6279d85ce el op0 op1 CRn op2 CRm t t2))
              else
                (do
                  if ((((((CRm == 0b0011#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                  then (do (TLBIP_VAE3IS_SysOpsWrite128_436ad5bd6c95d188 el op0 op1 CRn op2 CRm t t2))
                  else
                    (do
                      if ((((((CRm == 0b0011#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                      then (do (TLBIP_VAE3IS_SysOpsWrite128_41a3b7f5eb2783af el op0 op1 CRn op2 CRm t t2))
                      else
                        (do
                          if ((((((CRm == 0b0001#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                          then (do (TLBIP_VAE2OS_SysOpsWrite128_9f4cafd772ff7049 el op0 op1 CRn op2 CRm t t2))
                          else
                            (do
                              if ((((((CRm == 0b0001#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                              then (do (TLBIP_VAE2OS_SysOpsWrite128_a8e74684c20ce76a el op0 op1 CRn op2 CRm t t2))
                              else
                                (do
                                  if ((((((CRm == 0b0100#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                  then (do (TLBIP_IPAS2LE1_SysOpsWrite128_a67ad741d30f9316 el op0 op1 CRn op2 CRm t t2))
                                  else
                                    (do
                                      if ((((((CRm == 0b0100#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                      then (do (TLBIP_IPAS2LE1_SysOpsWrite128_0213d7545787eba6 el op0 op1 CRn op2 CRm t t2))
                                      else
                                        (do
                                          if ((((((CRm == 0b0011#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                          then (do (TLBIP_VAE1IS_SysOpsWrite128_642964df3a972e1f el op0 op1 CRn op2 CRm t t2))
                                          else
                                            (do
                                              if ((((((CRm == 0b0011#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                              then (do (TLBIP_VAE1IS_SysOpsWrite128_3c8e3a9292561f7f el op0 op1 CRn op2 CRm t t2))
                                              else
                                                (do
                                                  if ((((((CRm == 0b0011#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                  then (do (TLBIP_VALE3IS_SysOpsWrite128_c86e34b8232f3903 el op0 op1 CRn op2 CRm t t2))
                                                  else
                                                    (do
                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                      then (do (TLBIP_VALE3IS_SysOpsWrite128_df84b0484150f9e9 el op0 op1 CRn op2 CRm t t2))
                                                      else
                                                        (do
                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                          then (do (TLBIP_RVAE1IS_SysOpsWrite128_07c7343c7a06f43b el op0 op1 CRn op2 CRm t t2))
                                                          else
                                                            (do
                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                              then (do (TLBIP_RVAE1IS_SysOpsWrite128_7b5e59f759169cbe el op0 op1 CRn op2 CRm t t2))
                                                              else
                                                                (do
                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                  then (do (TLBIP_VALE1OS_SysOpsWrite128_3cce7186e158fbef el op0 op1 CRn op2 CRm t t2))
                                                                  else
                                                                    (do
                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                      then (do (TLBIP_VALE1OS_SysOpsWrite128_3dad834e560485db el op0 op1 CRn op2 CRm t t2))
                                                                      else
                                                                        (do
                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b110#3)) : Bool)
                                                                          then (do (TLBIP_RIPAS2LE1IS_SysOpsWrite128_86e34ca39816527e el op0 op1 CRn op2 CRm t t2))
                                                                          else
                                                                            (do
                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b110#3)) : Bool)
                                                                              then (do (TLBIP_RIPAS2LE1IS_SysOpsWrite128_e4198c9938d9ac42 el op0 op1 CRn op2 CRm t t2))
                                                                              else
                                                                                (do
                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                  then (do (TLBIP_VALE3OS_SysOpsWrite128_e22bb7777364db32 el op0 op1 CRn op2 CRm t t2))
                                                                                  else
                                                                                    (do
                                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                      then (do (TLBIP_VALE3OS_SysOpsWrite128_f558b9d9636e92e8 el op0 op1 CRn op2 CRm t t2))
                                                                                      else
                                                                                        (do
                                                                                          if ((((((CRm == 0b0101#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                          then (do (TLBIP_RVAE1OS_SysOpsWrite128_953ff681e796131f el op0 op1 CRn op2 CRm t t2))
                                                                                          else
                                                                                            (do
                                                                                              if ((((((CRm == 0b0101#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                              then (do (TLBIP_RVAE1OS_SysOpsWrite128_52f9177ad8036aaf el op0 op1 CRn op2 CRm t t2))
                                                                                              else
                                                                                                (do
                                                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                  then (do (TLBIP_RVALE2OS_SysOpsWrite128_4cbf07be986045b1 el op0 op1 CRn op2 CRm t t2))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((((((CRm == 0b0101#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                      then (do (TLBIP_RVALE2OS_SysOpsWrite128_cdc44a4c2d2759bb el op0 op1 CRn op2 CRm t t2))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                          then (do (TLBIP_RVALE3IS_SysOpsWrite128_2e388db98e6348e6 el op0 op1 CRn op2 CRm t t2))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                              then (do (TLBIP_RVALE3IS_SysOpsWrite128_46d9aa7cf0e1fea9 el op0 op1 CRn op2 CRm t t2))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                  then (do (TLBIP_RVAE2OS_SysOpsWrite128_056a89fd4c4c08d4 el op0 op1 CRn op2 CRm t t2))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((((((CRm == 0b0101#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                      then (do (TLBIP_RVAE2OS_SysOpsWrite128_e6b87760c99e44b3 el op0 op1 CRn op2 CRm t t2))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((((((CRm == 0b0100#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                          then (do (TLBIP_IPAS2E1_SysOpsWrite128_97574c637b9ec852 el op0 op1 CRn op2 CRm t t2))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((((((CRm == 0b0100#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                              then (do (TLBIP_IPAS2E1_SysOpsWrite128_769364ab2331c0c6 el op0 op1 CRn op2 CRm t t2))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                  then (do (TLBIP_RIPAS2E1IS_SysOpsWrite128_5606c3b58f00738a el op0 op1 CRn op2 CRm t t2))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                      then (do (TLBIP_RIPAS2E1IS_SysOpsWrite128_f1e0663ca68347ee el op0 op1 CRn op2 CRm t t2))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((((((CRm == 0b0011#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                          then (do (TLBIP_VAAE1IS_SysOpsWrite128_b3b4c6858b271cb2 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((((((CRm == 0b0011#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                              then (do (TLBIP_VAAE1IS_SysOpsWrite128_6f38dc04822d7f72 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                  then (do (TLBIP_VAE3OS_SysOpsWrite128_0bd4cb2b344ca9a6 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                      then (do (TLBIP_VAE3OS_SysOpsWrite128_7791c494d2ef59ef el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                          then (do (TLBIP_RVALE3_SysOpsWrite128_adcd898f13a55f9e el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                              then (do (TLBIP_RVALE3_SysOpsWrite128_6d1241c816962fe5 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((((((CRm == 0b0111#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                  then (do (TLBIP_VAALE1_SysOpsWrite128_ff6dfd8757e0cbb3 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                      then (do (TLBIP_VAALE1_SysOpsWrite128_9ce40ceffd0fb221 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((((((CRm == 0b0001#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                          then (do (TLBIP_VALE2OS_SysOpsWrite128_843e0c96a4c62b9d el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                              then (do (TLBIP_VALE2OS_SysOpsWrite128_a461faf4d3b82a3e el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((((((CRm == 0b0110#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                  then (do (TLBIP_RVAE2_SysOpsWrite128_86fa76bdb392deaa el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                      then (do (TLBIP_RVAE2_SysOpsWrite128_b5df47d526785ddb el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                          then (do (TLBIP_RVAAE1_SysOpsWrite128_2226e9154de9d452 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                              then (do (TLBIP_RVAAE1_SysOpsWrite128_9de89135f49c3abe el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                  then (do (TLBIP_IPAS2LE1IS_SysOpsWrite128_0a969d7a2aebccaa el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                      then (do (TLBIP_IPAS2LE1IS_SysOpsWrite128_ddc96d61f96d402c el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((((((CRm == 0b0111#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                          then (do (TLBIP_VAE3_SysOpsWrite128_46537a58be020b54 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((((((CRm == 0b0111#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                              then (do (TLBIP_VAE3_SysOpsWrite128_2fd14fc00c09a0fd el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((((((CRm == 0b0111#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                  then (do (TLBIP_VALE2_SysOpsWrite128_ad7af3eba7e26934 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                      then (do (TLBIP_VALE2_SysOpsWrite128_9b47499d61569e08 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((((((CRm == 0b0100#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                          then (do (TLBIP_RIPAS2LE1_SysOpsWrite128_2216f4b378e15ea4 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((((((CRm == 0b0100#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                              then (do (TLBIP_RIPAS2LE1_SysOpsWrite128_6b2d10467902cb52 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                  then (do (TLBIP_RVAE2IS_SysOpsWrite128_2948c6fb18c42d37 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((((((CRm == 0b0010#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                      then (do (TLBIP_RVAE2IS_SysOpsWrite128_37a80b444583dcfc el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                          then (do (TLBIP_RVAE1_SysOpsWrite128_f48006a3d9b88992 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                              then (do (TLBIP_RVAE1_SysOpsWrite128_b52389d29991d886 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                  then (do (TLBIP_RIPAS2E1_SysOpsWrite128_00618fa8e6f5ccba el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((((((CRm == 0b0100#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                      then (do (TLBIP_RIPAS2E1_SysOpsWrite128_027f5860c67e4500 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((((((match (CRm : BitVec 4) with
                                                                                                                                                                                                                                                                     | b__0 => true : Bool) && (let b__1 := CRn
                                                                                                                                                                                                                                                                     if ((((Sail.BitVec.extractLsb b__1 3 3) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__1 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                                                                                                                                                                                                                                                                     then true
                                                                                                                                                                                                                                                                     else false : Bool)) && (op0 == 0b01#2)) && (match (op1 : BitVec 3) with
                                                                                                                                                                                                                                                                 | b__2 => true : Bool)) && (match (op2 : BitVec 3) with
                                                                                                                                                                                                                                                               | b__3 => true : Bool)) : Bool)
                                                                                                                                                                                                                                                          then (do (S1_op1_Cn_Cm_op2_SysOpsWrite128_8cc8b9dd1f9a8cdc el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((((((CRm == 0b0100#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                              then (do (TLBIP_IPAS2E1OS_SysOpsWrite128_27f384221424e41f el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                  then (do (TLBIP_IPAS2E1OS_SysOpsWrite128_db7744f725bc7991 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                      then (do (TLBIP_VALE2IS_SysOpsWrite128_678498d40a585a6e el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0011#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                          then (do (TLBIP_VALE2IS_SysOpsWrite128_78fde03af9aaffc2 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0111#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                              then (do (TLBIP_VALE1_SysOpsWrite128_5f40ee04803f7fa0 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0111#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                  then (do (TLBIP_VALE1_SysOpsWrite128_eee3bc60168bedcf el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                      then (do (TLBIP_VALE3_SysOpsWrite128_da83d084586f123a el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0111#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                          then (do (TLBIP_VALE3_SysOpsWrite128_48fc2e32848138c0 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                              then (do (TLBIP_RVAALE1IS_SysOpsWrite128_216de9de0e6c2edd el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                  then (do (TLBIP_RVAALE1IS_SysOpsWrite128_b0040cdc6216868a el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0101#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                      then (do (TLBIP_RVALE3OS_SysOpsWrite128_4554dd46823f3440 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0101#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                          then (do (TLBIP_RVALE3OS_SysOpsWrite128_49511edcb37be47c el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0111#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                              then (do (TLBIP_VAAE1_SysOpsWrite128_b6cdb1aa6c90e3df el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0111#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_VAAE1_SysOpsWrite128_221a9e5bd861a7fa el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_VAE2_SysOpsWrite128_cf1b5c7d72a7a1dc el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0111#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_VAE2_SysOpsWrite128_6e51a4b4d32de64a el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0101#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_RVAAE1OS_SysOpsWrite128_6de8b9b690bdbc23 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_RVAAE1OS_SysOpsWrite128_4d5abc17d7bbb375 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0010#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_RVALE1IS_SysOpsWrite128_224b4e2dae034d4f el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_RVALE1IS_SysOpsWrite128_cf2c532882ecc547 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0011#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_VAE2IS_SysOpsWrite128_ed37b404a865a78e el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0011#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_VAE2IS_SysOpsWrite128_def0db16c10c82b4 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_VAE1_SysOpsWrite128_2afef2540faab1fa el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0111#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_VAE1_SysOpsWrite128_269036cb186b79de el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_RVAAE1IS_SysOpsWrite128_e47a2421133341a6 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_RVAAE1IS_SysOpsWrite128_137994942d296964 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0101#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_RVALE1OS_SysOpsWrite128_1b08f32f781f6c38 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0101#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_RVALE1OS_SysOpsWrite128_61edb4ff984a675a el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0101#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_RVAE3OS_SysOpsWrite128_2d1acd5b6076c150 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_RVAE3OS_SysOpsWrite128_33932d5a554256a9 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0101#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_RVAALE1OS_SysOpsWrite128_4c5726524a6ca4f1 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0101#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_RVAALE1OS_SysOpsWrite128_fb31802a92e4d6d3 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0011#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_VAALE1IS_SysOpsWrite128_351b0a0a4456682c el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0011#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_VAALE1IS_SysOpsWrite128_60f538ade9f32bfe el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0100#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_IPAS2LE1OS_SysOpsWrite128_84c03ae163aa7f64 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0100#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_IPAS2LE1OS_SysOpsWrite128_eb8e7b685976ccc1 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0011#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_VALE1IS_SysOpsWrite128_e79fa2efd56cba22 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0011#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_VALE1IS_SysOpsWrite128_b7a50d0df5ca047e el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_RVAE3_SysOpsWrite128_c37498e172f8a592 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_RVAE3_SysOpsWrite128_66b8dabb6e1234b5 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0100#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_RIPAS2E1OS_SysOpsWrite128_65e5b4cfbd986df8 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_RIPAS2E1OS_SysOpsWrite128_7ffb607d8c97e12e el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_VAAE1OS_SysOpsWrite128_edb83d9ce2a356a5 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0001#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_VAAE1OS_SysOpsWrite128_214fb682d8bbb61c el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_RVALE2_SysOpsWrite128_aba1731a5a045759 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0110#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_RVALE2_SysOpsWrite128_58a5be41d9a1fad2 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_RVAALE1_SysOpsWrite128_af1f37b9406d3bd8 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_RVAALE1_SysOpsWrite128_23742d31e3585c34 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0100#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_RIPAS2LE1OS_SysOpsWrite128_1423ee9208f18247 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_RIPAS2LE1OS_SysOpsWrite128_cd88b450d0aae1aa el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0001#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_VAE1OS_SysOpsWrite128_4fca314b90574242 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0001#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_VAE1OS_SysOpsWrite128_5f990b510a7de734 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_RVALE2IS_SysOpsWrite128_6ce0d3b37f2eb132 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_RVALE2IS_SysOpsWrite128_f13b8d96621db228 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      then (do (TLBIP_IPAS2E1IS_SysOpsWrite128_143f65c3f5ba3d9d el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          then (do (TLBIP_IPAS2E1IS_SysOpsWrite128_18df36996791819c el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1000#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              then (do (TLBIP_RVALE1_SysOpsWrite128_1ab99e0606965efe el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0110#4) && (CRn == 0b1001#4)) && (op0 == 0b01#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  then (do (TLBIP_RVALE1_SysOpsWrite128_a58a625d30647a57 el op0 op1 CRn op2 CRm t t2))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  else (AArch64_UnallocatedSysRegAccess op0 op1 CRn op2 CRm false t)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

