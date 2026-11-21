import Armv9.Flow
import Armv9.Prelude
import Armv9.V8Base
import Armv9.Stubs
import Armv9.SysregsAutogen.P04
import Armv9.SysregsAutogen.P07

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
def SPMEVTYPER_EL0_SysRegRead_fa3705a120ccce47 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))))))))))
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
                                      else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))))))))
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
                          else (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMEVTYPER_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMIIDR_EL1_SysRegRead_895b44f480e2fb64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      else (X_set t 64 (SPMIIDR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
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
                          else (X_set t 64 (SPMIIDR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMIIDR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMINTENCLR_EL1_SysRegRead_6d6d9e36e779f16f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMINTEN ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMINTEN (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMINTEN == 0#1)) : Bool)
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
                                      else (X_set t 64 (SPMINTENCLR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
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
                          else (X_set t 64 (SPMINTENCLR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMINTENCLR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMINTENSET_EL1_SysRegRead_93608e9ab6758704 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMINTEN ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMINTEN (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMINTEN == 0#1)) : Bool)
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
                                      else (X_set t 64 (SPMINTENSET_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
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
                          else (X_set t 64 (SPMINTENSET_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMINTENSET_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMOVSCLR_EL0_SysRegRead_f68ae6919a317d03 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMOVS ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMOVS (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMOVS == 0#1)) : Bool)
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
                                          else (X_set t 64 (SPMOVSCLR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMOVS == 0#1)) : Bool)
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
                                      else (X_set t 64 (SPMOVSCLR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
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
                          else (X_set t 64 (SPMOVSCLR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMOVSCLR_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMOVSSET_EL0_SysRegRead_5f97da0caf1e7976 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMOVS ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMOVS (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMOVS == 0#1)) : Bool)
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
                                          else (X_set t 64 (SPMOVSSET_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMOVS == 0#1)) : Bool)
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
                                      else (X_set t 64 (SPMOVSSET_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
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
                          else (X_set t 64 (SPMOVSSET_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (SPMOVSSET_EL0_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMROOTCR_EL3_SysRegRead_cc1acadd5685fbb1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (SPMROOTCR_EL3_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMSCR_EL1_SysRegRead_2d556bc720f0d5f6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR2_EL2_nSPMSCR_EL1 ← (( do (pure (_get_HDFGRTR2_EL2_Type_nSPMSCR_EL1 (← readReg HDFGRTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGRTR2_EL2_nSPMSCR_EL1 == 0#1)) : Bool)
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
                                          else (X_set t 64 (SPMSCR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))))))
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
                              else (X_set t 64 (SPMSCR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (SPMSCR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def S3_op1_Cn_Cm_op2_SysRegWrite_7b9e3d26ebc2fd52 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          else (AArch64_ImpDefSysRegWrite op0 op1 CRn CRm op2 t)))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TIDCP == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_ImpDefSysRegWrite op0 op1 CRn CRm op2 t))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch64_ImpDefSysRegWrite op0 op1 CRn CRm op2 t)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch64_ImpDefSysRegWrite op0 op1 CRn CRm op2 t)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMCNTENCLR_EL0_SysRegWrite_e212b08cd78070bd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMCNTEN ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMCNTEN (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMCNTEN == 0#1)) : Bool)
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
                                          else (pure (SPMCNTENCLR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMCNTEN == 0#1)) : Bool)
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
                                      else (pure (SPMCNTENCLR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))
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
                          else (pure (SPMCNTENCLR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMCNTENCLR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMCNTENSET_EL0_SysRegWrite_104b4f6a92dff98e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMCNTEN ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMCNTEN (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMCNTEN == 0#1)) : Bool)
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
                                          else (pure (SPMCNTENSET_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMCNTEN == 0#1)) : Bool)
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
                                      else (pure (SPMCNTENSET_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))
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
                          else (pure (SPMCNTENSET_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMCNTENSET_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMCR_EL0_SysRegWrite_869f53f4a7621978 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMCR_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMCR_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMCR_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMCR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMCR_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMCR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))
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
                          else (pure (SPMCR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMCR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_00cca0c3f5f0c589 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_07ced952b9f9c26f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_08629c5414f88eb2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_10b130ab758fd16f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_27dc77fd10e2aefe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_2ea680a33713cf5f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_3653857cd3f8b570 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_4e419851d7f8c37f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_5ea3d20a15000ec4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_73acab900a26c809 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_824f3bcfe3c44081 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_8ab800439a780c49 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_9c9ce3a923ecf708 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_b2918213479c6eeb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_be305c61a9d21074 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVCNTR_EL0_SysRegWrite_e5c1db8ac0393d51 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVCNTRn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVCNTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_15fbb8b13e7509b3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_229ceb05708f41b3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_2a7524fd36300597 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_2b5e3e8ebfdd2403 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_3d27f26840346448 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_3d2d295e35e201a9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_4603ea69874f5bc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_50419316a0793567 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_69501ae43204dc12 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_7e2235d697a1476e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_a4da6c90289f656a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_b606553f5e3a24b1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_cb01e2f00db2e33f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_e72797af60944ed4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_f8ad05ef8935cee4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILT2R_EL0_SysRegWrite_fc59638a1eed5ceb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILT2R_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_182705557e8ea81d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_20aefd1cb9d1a5ad (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_299c129e3abe1407 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_34f238c7595c6e75 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_437d4622cabaa331 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_63ddc3864e8582ee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_6ac937d3ce7c080c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_7801b81c1b7fe92f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_800cff4b7bbd47cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_88a821bdd88ae64a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_c6614df2d5b55f51 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_c7152a5fedd83db1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_d5a6ac5fd18a3308 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_e6a6baf23bbccd94 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_ecb12bf267c7f798 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_f1320088845e7cb6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))))))
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
                         (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                          else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64)))))))))
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
                  else (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_098b2f43a6b02fc6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 9) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_2378547a2e24476f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 6) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_4393696836cb717a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 12) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_46f7fc9c89e9ac28 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 0) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_4cd57f5297b70cc6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 1) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_5025c58a115fd550 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 4) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_7dce83dc121838ba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 3) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_91f23b951f61a56d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 7) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_93c3d2ea6e6e387c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 5) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_99f1a4973d26a8c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 13) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_ccaf15f0e189ded0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 14) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_d04d1aa656252a7a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 2) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_dbe2b870ee80c8aa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 11) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_df46bde4a98df889 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 10) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_f79086ccec170944 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 15) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMEVTYPER_EL0_SysRegWrite_f9120e686bac1284 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_EnSPM ← (( do (pure (_get_MDSCR_EL1_Type_EnSPM (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                                 (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))))))))))
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1)) : Bool)
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
                                      else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))))))))
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
                          else (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMEVTYPER_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK (← readReg SPMSELR_EL0))) *i 16) +i 8) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMINTENCLR_EL1_SysRegWrite_26843e073959385e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMINTEN ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMINTEN (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMINTEN == 0#1)) : Bool)
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
                                      else (pure (SPMINTENCLR_EL1_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))
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
                          else (pure (SPMINTENCLR_EL1_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMINTENCLR_EL1_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def SPMINTENSET_EL1_SysRegWrite_9368dd5ceffac1da (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_EnPM2 ← (( do (pure (_get_MDCR_EL3_Type_EnPM2 (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn2 ← (( do (pure (_get_SCR_EL3_Type_FGTEn2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR2_EL2_nSPMINTEN ← (( do (pure (_get_HDFGWTR2_EL2_Type_nSPMINTEN (← readReg HDFGWTR2_EL2))) ) : SailM (BitVec 1) )
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
                             (IsFeatureImplemented FEAT_FGT2)))) && (__HDFGWTR2_EL2_nSPMINTEN == 0#1)) : Bool)
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
                                      else (pure (SPMINTENSET_EL1_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))))))
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
                          else (pure (SPMINTENSET_EL1_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (pure (SPMINTENSET_EL1_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) (← (X_read t 64))))
              else (pure ()))))


