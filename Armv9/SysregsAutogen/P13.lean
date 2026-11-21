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
def ICC_BPR1_SysRegWrite32_fa0a3cea06e15e3e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_IRQ ← (( do (pure (_get_SCR_Type_IRQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL1 ← (( do (pure (_get_ICH_HCR_Type_TALL1 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_IMO ← (( do (pure (_get_HCR_Type_IMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_IRQ == 1#1)) : Bool)
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
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__ICH_HCR_TALL1 == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                      then (ICV_BPR1_write (Mk_ICV_BPR1_Type (← (R_read t))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                          then (ICV_BPR1_write (Mk_ICV_BPR1_Type (← (R_read t))))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                              else
                                                (do
                                                  if ((((←((pure (HaveEL EL3)) <&&> (do
                                                           (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_IRQ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      if ((←((Halted ()) <&&> (do
                                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                      else (AArch32_TakeMonitorTrapException ()))
                                                  else
                                                    (do
                                                      if ((HaveEL EL3) : Bool)
                                                      then (ICC_BPR1_NS_write (Mk_ICC_BPR1_Type (← (R_read t))))
                                                      else (ICC_BPR1_write (Mk_ICC_BPR1_Type (← (R_read t))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_IRQ == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (ELUsingAArch32 EL3)))) && (__SCR_IRQ == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch32_TakeMonitorTrapException ()))
                              else
                                (do
                                  if ((HaveEL EL3) : Bool)
                                  then (ICC_BPR1_NS_write (Mk_ICC_BPR1_Type (← (R_read t))))
                                  else (ICC_BPR1_write (Mk_ICC_BPR1_Type (← (R_read t))))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (ICC_BPR1_S_write (Mk_ICC_BPR1_Type (← (R_read t))))
                      else (ICC_BPR1_NS_write (Mk_ICC_BPR1_Type (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_DIR_SysRegWrite32_5d925e0a6cd7195a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TDIR ← (( do (pure (_get_ICH_HCR_EL2_Type_TDIR (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TC ← (( do (pure (_get_ICH_HCR_EL2_Type_TC (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TC ← (( do (pure (_get_ICH_HCR_Type_TC (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TDIR ← (( do (pure (_get_ICH_HCR_Type_TDIR (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
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
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TDIR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
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
                                             (ELUsingAArch32 EL2)))) && (__ICH_HCR_TDIR == 1#1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FMO == 1#1)) : Bool)
                                          then (ICV_DIR_write (Mk_ICV_DIR_Type (← (R_read t))))
                                          else
                                            (do
                                              if (((←((EL2Enabled ()) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                              then (ICV_DIR_write (Mk_ICV_DIR_Type (← (R_read t))))
                                              else
                                                (do
                                                  if (((←((EL2Enabled ()) <&&> (do
                                                         (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                                  then (ICV_DIR_write (Mk_ICV_DIR_Type (← (R_read t))))
                                                  else
                                                    (do
                                                      if (((←((EL2Enabled ()) <&&> (do
                                                             (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                                      then (ICV_DIR_write (Mk_ICV_DIR_Type (← (R_read t))))
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
                                                              else (ICC_DIR_write (Mk_ICC_DIR_Type (← (R_read t))))))))))))))))))
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
                              else (ICC_DIR_write (Mk_ICC_DIR_Type (← (R_read t)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICC_DIR_write (Mk_ICC_DIR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_EOIR1_SysRegWrite32_b67c881f4f810bd8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_IRQ ← (( do (pure (_get_SCR_Type_IRQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL1 ← (( do (pure (_get_ICH_HCR_Type_TALL1 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
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
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_IRQ == 1#1)) : Bool)
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
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__ICH_HCR_TALL1 == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                      then (ICV_EOIR1_write (Mk_ICV_EOIR1_Type (← (R_read t))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                          then (ICV_EOIR1_write (Mk_ICV_EOIR1_Type (← (R_read t))))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                              else
                                                (do
                                                  if ((((←((pure (HaveEL EL3)) <&&> (do
                                                           (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_IRQ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      if ((←((Halted ()) <&&> (do
                                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                      else (AArch32_TakeMonitorTrapException ()))
                                                  else (ICC_EOIR1_write (Mk_ICC_EOIR1_Type (← (R_read t)))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_IRQ == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (ELUsingAArch32 EL3)))) && (__SCR_IRQ == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch32_TakeMonitorTrapException ()))
                              else (ICC_EOIR1_write (Mk_ICC_EOIR1_Type (← (R_read t)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICC_EOIR1_write (Mk_ICC_EOIR1_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_HSRE_SysRegWrite32_3352216733a79da7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL3_Enable ← (( do (pure (_get_ICC_SRE_EL3_Type_Enable (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_Enable ← (( do (pure (_get_ICC_MSRE_Type_Enable (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      if ((__ICC_MSRE_Enable == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (ICC_HSRE_write (Mk_ICC_HSRE_Type (← (R_read t)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICC_HSRE_write (Mk_ICC_HSRE_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_MCTLR_SysRegWrite32_c2e3c881e988dc90 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg ICC_MCTLR (Mk_ICC_MCTLR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_MGRPEN1_SysRegWrite32_a295be12c6cd3191 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg ICC_MGRPEN1 (Mk_ICC_MGRPEN1_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_MSRE_SysRegWrite32_3238a1354a48916c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((BEq.beq (← readReg CP15SDISABLE2) Signal_High) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else writeReg ICC_MSRE (Mk_ICC_MSRE_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_PMR_SysRegWrite32_b23a221ce6bd2853 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                                  then (ICV_PMR_write (Mk_ICV_PMR_Type (← (R_read t))))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                      then (ICV_PMR_write (Mk_ICV_PMR_Type (← (R_read t))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (ICV_PMR_write (Mk_ICV_PMR_Type (← (R_read t))))
                                          else
                                            (do
                                              if (((←((EL2Enabled ()) <&&> (do
                                                     (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                              then (ICV_PMR_write (Mk_ICV_PMR_Type (← (R_read t))))
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
                                                      else (ICC_PMR_write (Mk_ICC_PMR_Type (← (R_read t))))))))))))))))
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
                              else (ICC_PMR_write (Mk_ICC_PMR_Type (← (R_read t)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICC_PMR_write (Mk_ICC_PMR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_SRE_SysRegWrite32_9b4f583336a77d42 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __ICC_SRE_EL3_Enable ← (( do (pure (_get_ICC_SRE_EL3_Type_Enable (← readReg ICC_SRE_EL3))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_EL2_Enable ← (( do (pure (_get_ICC_SRE_EL2_Type_Enable (← readReg ICC_SRE_EL2))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_Enable ← (( do (pure (_get_ICC_HSRE_Type_Enable (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_Enable ← (( do (pure (_get_ICC_MSRE_Type_Enable (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
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
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICC_SRE_EL2_Enable == 0#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__ICC_HSRE_Enable == 0#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (ELUsingAArch32 EL3)))) && (__ICC_MSRE_Enable == 0#1)) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((HaveEL EL3) : Bool)
                                      then
                                        (do
                                          if ((__SCR_EL3_NS == 0#1) : Bool)
                                          then (ICC_SRE_S_write (Mk_ICC_SRE_Type (← (R_read t))))
                                          else (ICC_SRE_NS_write (Mk_ICC_SRE_Type (← (R_read t)))))
                                      else (ICC_SRE_write (Mk_ICC_SRE_Type (← (R_read t))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__ICC_SRE_EL3_Enable == 0#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      if ((__ICC_MSRE_Enable == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if ((HaveEL EL3) : Bool)
                          then
                            (do
                              if ((__SCR_EL3_NS == 0#1) : Bool)
                              then (ICC_SRE_S_write (Mk_ICC_SRE_Type (← (R_read t))))
                              else (ICC_SRE_NS_write (Mk_ICC_SRE_Type (← (R_read t)))))
                          else (ICC_SRE_write (Mk_ICC_SRE_Type (← (R_read t))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (ICC_SRE_S_write (Mk_ICC_SRE_Type (← (R_read t))))
                  else (ICC_SRE_NS_write (Mk_ICC_SRE_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegWrite32_0687237dd975d38e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegWrite32_776121746bc0b6a3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_AP0R_set 0 (Mk_ICH_AP0R_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_AP0R_set 0 (Mk_ICH_AP0R_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegWrite32_e8bf01c9f2e53161 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegWrite32_e8e0b6211baf6183 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegWrite32_100dab3ceee19d37 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegWrite32_28a69956588386f7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_AP1R_set 0 (Mk_ICH_AP1R_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_AP1R_set 0 (Mk_ICH_AP1R_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegWrite32_4eff4ec729dbfa39 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegWrite32_9d0709acdf26e0db (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_HCR_SysRegWrite32_391df800f72b5649 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_HCR_write (Mk_ICH_HCR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_HCR_write (Mk_ICH_HCR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_26a1b63afe3dfd72 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 11 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 11 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_386394d9b9080275 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 7 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 7 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_43a5c55815de94d9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 9 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 9 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_5036a59d7b5ab1d9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 13 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 13 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_51763a756078a699 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 8 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 8 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_5dd9fb114b3c7d62 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 12 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 12 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_9511e78c9b2df1ea (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 1 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 1 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_9859737df8ae4807 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 6 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 6 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_a1a007d19312bc57 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 5 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 5 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_b623b068212a51e1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 4 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 4 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_bc7eed7f83c8b68e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 10 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 10 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_dfd8b885b691ae03 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 2 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 2 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_e225401f886e4760 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 3 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 3 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_ed5a361acf9b81f0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 15 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 15 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_f00162b6acc3532f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 14 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 14 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegWrite32_fa0ed50b180dc30b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LRC_set 0 (Mk_ICH_LRC_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LRC_set 0 (Mk_ICH_LRC_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_2360c70ac77c896c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 3 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 3 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_29c49b66d9046e0a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 0 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 0 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_2e1b19b394d8f1f7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 15 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 15 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_514fb9fa160b7dee (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 9 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 9 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_5f330d948f9246f1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 4 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 4 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_64e5be949dba10fe (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 2 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 2 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_66cfea86c7608fe1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 1 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 1 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_69f059200b508494 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 7 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 7 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_721fa51d485f4b0a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 8 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 8 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_8da50c378e183c13 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 12 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 12 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_9a10116a6dad894d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 14 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 14 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_a7e50c74ffa894c4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 13 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 13 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_c3bfb21b3a349563 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 10 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 10 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_d1e236ff7c3dc751 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 5 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 5 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_eaa9053ceb4916d6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 6 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 6 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegWrite32_f689ea0e1ff8a941 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_LR_set 11 (Mk_ICH_LR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_LR_set 11 (Mk_ICH_LR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_VMCR_SysRegWrite32_2eb356e2f10a122b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
          then
            (do
              if ((__ICC_HSRE_SRE == 0#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (ICH_VMCR_write (Mk_ICH_VMCR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICH_VMCR_write (Mk_ICH_VMCR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICIALLUIS_SysRegWrite32_33170c116ea45e36 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPU ← (( do (pure (_get_HCR_EL2_Type_TPU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TICAB ← (( do (pure (_get_HCR_EL2_Type_TICAB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TPU ← (( do (pure (_get_HCR_Type_TPU (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TICAB ← (( do (pure (_get_HCR2_Type_TICAB (← (HCR2_read ())))) ) : SailM (BitVec 1) )
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TPU == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TICAB == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TPU == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TICAB == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch32_IC CacheOpScope_ALLUIS)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_IC CacheOpScope_ALLUIS)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_IC CacheOpScope_ALLUIS)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICIALLU_SysRegWrite32_cbf11f5ea46a9ef3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPU ← (( do (pure (_get_HCR_EL2_Type_TPU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TOCU ← (( do (pure (_get_HCR_EL2_Type_TOCU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TPU ← (( do (pure (_get_HCR_Type_TPU (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TOCU ← (( do (pure (_get_HCR2_Type_TOCU (← (HCR2_read ())))) ) : SailM (BitVec 1) )
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TPU == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TOCU == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TPU == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TOCU == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HCR_FB == 1#1)) : Bool)
                                  then (AArch32_IC CacheOpScope_ALLUIS)
                                  else (AArch32_IC CacheOpScope_ALLU))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_IC CacheOpScope_ALLU)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_IC CacheOpScope_ALLU)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICIMVAU_SysRegWrite32_98e4788d39c19ba0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T7 ← (( do (pure (_get_HSTR_EL2_Type_T7 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T7 ← (( do (pure (_get_HSTR_Type_T7 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TPU ← (( do (pure (_get_HCR_EL2_Type_TPU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TOCU ← (( do (pure (_get_HCR_EL2_Type_TOCU (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TPU ← (( do (pure (_get_HCR_Type_TPU (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR2_TOCU ← (( do (pure (_get_HCR2_Type_TOCU (← (HCR2_read ())))) ) : SailM (BitVec 1) )
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
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TPU == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TOCU == 1#1)) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (ELUsingAArch32 EL2)))) && (__HCR_TPU == 1#1)) : Bool)
                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TOCU == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else (AArch32_IC__1 (← (R_read t)) CacheOpScope_PoU)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_IC__1 (← (R_read t)) CacheOpScope_PoU)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_IC__1 (← (R_read t)) CacheOpScope_PoU)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_AP0R_SysRegWrite32_7420f74019631696 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_FIQ ← (( do (pure (_get_SCR_Type_FIQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL0 ← (( do (pure (_get_ICH_HCR_Type_TALL0 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FMO ← (( do (pure (_get_HCR_Type_FMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICV_AP0R_SysRegWrite32_b2c1de53009da653 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_FIQ ← (( do (pure (_get_SCR_Type_FIQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL0 ← (( do (pure (_get_ICH_HCR_Type_TALL0 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FMO ← (( do (pure (_get_HCR_Type_FMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_FIQ == 1#1)) : Bool)
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
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TALL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__ICH_HCR_TALL0 == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FMO == 1#1)) : Bool)
                                      then (ICV_AP0R_set 0 (← (R_read t)))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (ICV_AP0R_set 0 (← (R_read t)))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                              else
                                                (do
                                                  if ((((←((pure (HaveEL EL3)) <&&> (do
                                                           (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_FIQ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      if ((←((Halted ()) <&&> (do
                                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                      else (AArch32_TakeMonitorTrapException ()))
                                                  else (ICC_AP0R_set 0 (← (R_read t))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_FIQ == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (ELUsingAArch32 EL3)))) && (__SCR_FIQ == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch32_TakeMonitorTrapException ()))
                              else (ICC_AP0R_set 0 (← (R_read t))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICC_AP0R_set 0 (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_AP0R_SysRegWrite32_c1e479184edb7511 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_FIQ ← (( do (pure (_get_SCR_Type_FIQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL0 ← (( do (pure (_get_ICH_HCR_Type_TALL0 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FMO ← (( do (pure (_get_HCR_Type_FMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICV_AP0R_SysRegWrite32_f5921a0effda4992 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_FIQ ← (( do (pure (_get_SCR_Type_FIQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL0 ← (( do (pure (_get_ICH_HCR_Type_TALL0 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FMO ← (( do (pure (_get_HCR_Type_FMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICV_AP1R_SysRegWrite32_4f1e8bd1c2644b3a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_IRQ ← (( do (pure (_get_SCR_Type_IRQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL1 ← (( do (pure (_get_ICH_HCR_Type_TALL1 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_IMO ← (( do (pure (_get_HCR_Type_IMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICV_AP1R_SysRegWrite32_726e2b6e8a63f123 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_IRQ ← (( do (pure (_get_SCR_Type_IRQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL1 ← (( do (pure (_get_ICH_HCR_Type_TALL1 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_IMO ← (( do (pure (_get_HCR_Type_IMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICV_AP1R_SysRegWrite32_f4f5f3a432a35847 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_IRQ ← (( do (pure (_get_SCR_Type_IRQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL1 ← (( do (pure (_get_ICH_HCR_Type_TALL1 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_IMO ← (( do (pure (_get_HCR_Type_IMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICV_AP1R_SysRegWrite32_fcd6d6e80a079de9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_IRQ ← (( do (pure (_get_SCR_Type_IRQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL1 ← (( do (pure (_get_ICH_HCR_Type_TALL1 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_IMO ← (( do (pure (_get_HCR_Type_IMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_IRQ == 1#1)) : Bool)
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
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__ICH_HCR_TALL1 == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                      then (ICV_AP1R_set 0 (← (R_read t)))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                          then (ICV_AP1R_set 0 (← (R_read t)))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                              else
                                                (do
                                                  if ((((←((pure (HaveEL EL3)) <&&> (do
                                                           (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_IRQ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      if ((←((Halted ()) <&&> (do
                                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                      else (AArch32_TakeMonitorTrapException ()))
                                                  else
                                                    (do
                                                      if ((HaveEL EL3) : Bool)
                                                      then (ICC_AP1R_NS_set 0 (← (R_read t)))
                                                      else (ICC_AP1R_set 0 (← (R_read t)))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_IRQ == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (ELUsingAArch32 EL3)))) && (__SCR_IRQ == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch32_TakeMonitorTrapException ()))
                              else
                                (do
                                  if ((HaveEL EL3) : Bool)
                                  then (ICC_AP1R_NS_set 0 (← (R_read t)))
                                  else (ICC_AP1R_set 0 (← (R_read t)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (ICC_AP1R_S_set 0 (← (R_read t)))
                      else (ICC_AP1R_NS_set 0 (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_CTLR_SysRegWrite32_6f9cee422585c5f5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TC ← (( do (pure (_get_ICH_HCR_EL2_Type_TC (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TC ← (( do (pure (_get_ICH_HCR_Type_TC (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FMO ← (( do (pure (_get_HCR_Type_FMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_IMO ← (( do (pure (_get_HCR_Type_IMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
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
                                  then (ICV_CTLR_write (Mk_ICV_CTLR_Type (← (R_read t))))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                      then (ICV_CTLR_write (Mk_ICV_CTLR_Type (← (R_read t))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (ICV_CTLR_write (Mk_ICV_CTLR_Type (← (R_read t))))
                                          else
                                            (do
                                              if (((←((EL2Enabled ()) <&&> (do
                                                     (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                              then (ICV_CTLR_write (Mk_ICV_CTLR_Type (← (R_read t))))
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
                                                      else
                                                        (do
                                                          if ((HaveEL EL3) : Bool)
                                                          then (ICC_CTLR_NS_write (Mk_ICC_CTLR_Type (← (R_read t))))
                                                          else (ICC_CTLR_write (Mk_ICC_CTLR_Type (← (R_read t)))))))))))))))))
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
                              else
                                (do
                                  if ((HaveEL EL3) : Bool)
                                  then (ICC_CTLR_NS_write (Mk_ICC_CTLR_Type (← (R_read t))))
                                  else (ICC_CTLR_write (Mk_ICC_CTLR_Type (← (R_read t))))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (ICC_CTLR_S_write (Mk_ICC_CTLR_Type (← (R_read t))))
                      else (ICC_CTLR_NS_write (Mk_ICC_CTLR_Type (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_EOIR0_SysRegWrite32_a5e151ee536f5632 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_FIQ ← (( do (pure (_get_SCR_Type_FIQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL0 ← (( do (pure (_get_ICH_HCR_Type_TALL0 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FMO ← (( do (pure (_get_HCR_Type_FMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_FIQ == 1#1)) : Bool)
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
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TALL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__ICH_HCR_TALL0 == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FMO == 1#1)) : Bool)
                                      then (ICV_EOIR0_write (Mk_ICV_EOIR0_Type (← (R_read t))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (ICV_EOIR0_write (Mk_ICV_EOIR0_Type (← (R_read t))))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                              else
                                                (do
                                                  if ((((←((pure (HaveEL EL3)) <&&> (do
                                                           (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_FIQ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      if ((←((Halted ()) <&&> (do
                                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                      else (AArch32_TakeMonitorTrapException ()))
                                                  else (ICC_EOIR0_write (Mk_ICC_EOIR0_Type (← (R_read t)))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_FIQ == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (ELUsingAArch32 EL3)))) && (__SCR_FIQ == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch32_TakeMonitorTrapException ()))
                              else (ICC_EOIR0_write (Mk_ICC_EOIR0_Type (← (R_read t)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICC_EOIR0_write (Mk_ICC_EOIR0_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_IGRPEN0_SysRegWrite32_e641a403de7ed22c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_FIQ ← (( do (pure (_get_SCR_EL3_Type_FIQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_FIQ ← (( do (pure (_get_SCR_Type_FIQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL0 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL0 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL0 ← (( do (pure (_get_ICH_HCR_Type_TALL0 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_FMO ← (( do (pure (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_FMO ← (( do (pure (_get_HCR_Type_FMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_FIQ == 1#1)) : Bool)
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
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TALL0 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__ICH_HCR_TALL0 == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_FMO == 1#1)) : Bool)
                                      then (ICV_IGRPEN0_write (Mk_ICV_IGRPEN0_Type (← (R_read t))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (ICV_IGRPEN0_write (Mk_ICV_IGRPEN0_Type (← (R_read t))))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                              else
                                                (do
                                                  if ((((←((pure (HaveEL EL3)) <&&> (do
                                                           (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_FIQ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      if ((←((Halted ()) <&&> (do
                                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                      else (AArch32_TakeMonitorTrapException ()))
                                                  else (ICC_IGRPEN0_write (Mk_ICC_IGRPEN0_Type (← (R_read t)))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_FIQ == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_FIQ == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (ELUsingAArch32 EL3)))) && (__SCR_FIQ == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch32_TakeMonitorTrapException ()))
                              else (ICC_IGRPEN0_write (Mk_ICC_IGRPEN0_Type (← (R_read t)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (ICC_IGRPEN0_write (Mk_ICC_IGRPEN0_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_IGRPEN1_SysRegWrite32_224f633a4805f3d5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_IRQ ← (( do (pure (_get_SCR_EL3_Type_IRQ (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  let __SCR_IRQ ← (( do (pure (_get_SCR_Type_IRQ (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_SRE_SRE ← (( do (pure (_get_ICC_SRE_Type_SRE (← (ICC_SRE_read ())))) ) : SailM (BitVec 1) )
  let __ICH_HCR_EL2_TALL1 ← (( do (pure (_get_ICH_HCR_EL2_Type_TALL1 (← readReg ICH_HCR_EL2))) ) : SailM (BitVec 1) )
  let __ICH_HCR_TALL1 ← (( do (pure (_get_ICH_HCR_Type_TALL1 (← (ICH_HCR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_IMO ← (( do (pure (_get_HCR_EL2_Type_IMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_IMO ← (( do (pure (_get_HCR_Type_IMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  let __SCR_NS ← (( do (pure (_get_SCR_Type_NS (← readReg SCR))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                       (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_IRQ == 1#1)) : Bool)
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
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__ICH_HCR_EL2_TALL1 == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__ICH_HCR_TALL1 == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                      then (ICV_IGRPEN1_write (Mk_ICV_IGRPEN1_Type (← (R_read t))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                          then (ICV_IGRPEN1_write (Mk_ICV_IGRPEN1_Type (← (R_read t))))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                              else
                                                (do
                                                  if ((((←((pure (HaveEL EL3)) <&&> (do
                                                           (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_IRQ == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      if ((←((Halted ()) <&&> (do
                                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                      else (AArch32_TakeMonitorTrapException ()))
                                                  else
                                                    (do
                                                      if ((HaveEL EL3) : Bool)
                                                      then (ICC_IGRPEN1_NS_write (Mk_ICC_IGRPEN1_Type (← (R_read t))))
                                                      else (ICC_IGRPEN1_write (Mk_ICC_IGRPEN1_Type (← (R_read t))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_IRQ == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_IRQ == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (ELUsingAArch32 EL3)))) && (__SCR_IRQ == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch32_TakeMonitorTrapException ()))
                              else
                                (do
                                  if ((HaveEL EL3) : Bool)
                                  then (ICC_IGRPEN1_NS_write (Mk_ICC_IGRPEN1_Type (← (R_read t))))
                                  else (ICC_IGRPEN1_write (Mk_ICC_IGRPEN1_Type (← (R_read t))))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then (ICC_IGRPEN1_S_write (Mk_ICC_IGRPEN1_Type (← (R_read t))))
                      else (ICC_IGRPEN1_NS_write (Mk_ICC_IGRPEN1_Type (← (R_read t))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def IFAR_SysRegWrite32_7cf35b53506c7522 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T6 ← (( do (pure (_get_HSTR_EL2_Type_T6 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T6 ← (( do (pure (_get_HSTR_Type_T6 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T6 == 1#1)) : Bool)
          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (ELUsingAArch32 EL2)))) && (__HSTR_T6 == 1#1)) : Bool)
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
                          then (IFAR_NS_write (← (R_read t)))
                          else (IFAR_write (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (IFAR_NS_write (← (R_read t)))
              else (IFAR_write (← (R_read t))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (IFAR_S_write (← (R_read t)))
                  else (IFAR_NS_write (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def IFSR_SysRegWrite32_86456fc11d1622be (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          then (IFSR_NS_write (Mk_IFSR_Type (← (R_read t))))
                          else (IFSR_write (Mk_IFSR_Type (← (R_read t)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (IFSR_NS_write (Mk_IFSR_Type (← (R_read t))))
              else (IFSR_write (Mk_IFSR_Type (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg IFSR_S (Mk_IFSR_Type (← (R_read t)))
                  else (IFSR_NS_write (Mk_IFSR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ITLBIALL_SysRegWrite32_58b4810189599a79 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
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
                             (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                 (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                 (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                          then (AArch32_ITLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_NSH TLBI_ExcludeXS)
                          else (AArch32_ITLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_NSH TLBI_AllAttr))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_ITLBI_ALL (← (SecurityStateAtEL EL1)) Regime_EL10 Shareability_NSH TLBI_AllAttr)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_ITLBI_ALL (← (SecurityStateAtEL EL3)) Regime_EL30 Shareability_NSH TLBI_AllAttr)
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ITLBIASID_SysRegWrite32_4c595ca2314b7198 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
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
                             (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                 (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                 (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                          then (AArch32_ITLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_ExcludeXS (← (R_read t)))
                          else (AArch32_ITLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_ITLBI_ASID (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_ITLBI_ASID (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_NSH TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ITLBIMVA_SysRegWrite32_ff4131cdf091f782 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T8 ← (( do (pure (_get_HSTR_EL2_Type_T8 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T8 ← (( do (pure (_get_HSTR_Type_T8 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TTLB ← (( do (pure (_get_HCR_EL2_Type_TTLB (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_TTLB ← (( do (pure (_get_HCR_Type_TTLB (← (HCR_read ())))) ) : SailM (BitVec 1) )
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
                             (ELUsingAArch32 EL2)))) && (__HCR_TTLB == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                      else
                        (do
                          if (((←((IsFeatureImplemented FEAT_XS) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                 (IsFeatureImplemented FEAT_HCX)) <&&> (do
                                 (IsHCRXEL2Enabled ())))) && (__HCRX_EL2_FnXS == 1#1)) : Bool)
                          then (AArch32_ITLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_ExcludeXS (← (R_read t)))
                          else (AArch32_ITLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (AArch32_ITLBI_VA (← (SecurityStateAtEL EL1)) Regime_EL10 (← (VMID_read ())) Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (AArch32_ITLBI_VA (← (SecurityStateAtEL EL3)) Regime_EL30 VMID_NONE Shareability_NSH TLBILevel_Any TLBI_AllAttr (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def JMCR_SysRegWrite32_5cdfe87c581e3185 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (__IMPDEF_boolean "JMCR UNDEFINED at EL0")) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ()))
  else
    (if ((__PSTATE_EL == EL1) : Bool)
    then (pure ())
    else
      (if ((__PSTATE_EL == EL2) : Bool)
      then (pure ())
      else
        (if ((__PSTATE_EL == EL3) : Bool)
        then (pure ())
        else (pure ()))))

/-- Type quantifiers: t : Int -/
def JOSCR_SysRegWrite32_88e20b8662c98b9c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (__IMPDEF_boolean "JOSCR UNDEFINED at EL0")) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ()))
  else
    (if ((__PSTATE_EL == EL1) : Bool)
    then (pure ())
    else
      (if ((__PSTATE_EL == EL2) : Bool)
      then (pure ())
      else
        (if ((__PSTATE_EL == EL3) : Bool)
        then (pure ())
        else (pure ()))))

/-- Type quantifiers: t : Int -/
def MVBAR_SysRegWrite32_b51bf66bf3dc6e40 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
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
                  if ((BEq.beq (← readReg CP15SDISABLE) Signal_High) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((BEq.beq (← readReg CP15SDISABLE2) Signal_High) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else writeReg MVBAR (Mk_MVBAR_Type (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def NMRR_SysRegWrite32_d7c63fb9ed572aa1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              then (MAIR1_NS_write (Mk_MAIR1_Type (← (R_read t))))
                              else (NMRR_NS_write (Mk_NMRR_Type (← (R_read t)))))
                          else
                            (do
                              if ((← (EAEisOne ())) : Bool)
                              then (MAIR1_write (Mk_MAIR1_Type (← (R_read t))))
                              else (NMRR_write (Mk_NMRR_Type (← (R_read t))))))))))
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
                  then (MAIR1_NS_write (Mk_MAIR1_Type (← (R_read t))))
                  else (NMRR_NS_write (Mk_NMRR_Type (← (R_read t)))))
              else
                (do
                  if ((← (EAEisOne ())) : Bool)
                  then (MAIR1_write (Mk_MAIR1_Type (← (R_read t))))
                  else (NMRR_write (Mk_NMRR_Type (← (R_read t))))))
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
                              then (MAIR1_S_write (Mk_MAIR1_Type (← (R_read t))))
                              else (MAIR1_NS_write (Mk_MAIR1_Type (← (R_read t)))))
                          else
                            (do
                              if ((__SCR_NS == 0#1) : Bool)
                              then writeReg NMRR_S (Mk_NMRR_Type (← (R_read t)))
                              else (NMRR_NS_write (Mk_NMRR_Type (← (R_read t))))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def NSACR_SysRegWrite32_78181d9f16e34b35 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else writeReg NSACR (Mk_NSACR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PAR_SysRegWrite32_b3494b8d6e542bfa (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else
                (do
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (ELUsingAArch32 EL3)))) : Bool)
                  then writeReg PAR_NS (Sail.BitVec.updateSubrange (← readReg PAR_NS) 31 0 (← (R_read t)))
                  else (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange (← (PAR_read ())) 31 0 (← (R_read t))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then writeReg PAR_NS (Sail.BitVec.updateSubrange (← readReg PAR_NS) 31 0 (← (R_read t)))
              else (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange (← (PAR_read ())) 31 0 (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then writeReg PAR_S (Sail.BitVec.updateSubrange (← readReg PAR_S) 31 0 (← (R_read t)))
                  else writeReg PAR_NS (Sail.BitVec.updateSubrange (← readReg PAR_NS) 31 0 (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCCFILTR_SysRegWrite32_380c0e93b25f3214 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMCCFILTR_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMCCFILTR_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMCCFILTR_EL0 == 1#1)) : Bool)
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
                              else (PMCCFILTR_write (Mk_PMCCFILTR_Type (← (R_read t)))))))))))
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
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else (PMCCFILTR_write (Mk_PMCCFILTR_Type (← (R_read t))))))))
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
                  else (PMCCFILTR_write (Mk_PMCCFILTR_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMCCFILTR_write (Mk_PMCCFILTR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCCNTR_SysRegWrite32_2765928b3dd6404e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMCCNTR_EL0 == 1#1)) : Bool)
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
                                      else (PMCCNTR_write (Mk_PMCCNTR_Type (Sail.BitVec.updateSubrange (← (PMCCNTR_read ())) 31 0 (← (R_read t))))))))))))))
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
                              else (PMCCNTR_write (Mk_PMCCNTR_Type (Sail.BitVec.updateSubrange (← (PMCCNTR_read ())) 31 0 (← (R_read t)))))))))))
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
                  else (PMCCNTR_write (Mk_PMCCNTR_Type (Sail.BitVec.updateSubrange (← (PMCCNTR_read ())) 31 0 (← (R_read t)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMCCNTR_write (Mk_PMCCNTR_Type (Sail.BitVec.updateSubrange (← (PMCCNTR_read ())) 31 0 (← (R_read t)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCNTENCLR_SysRegWrite32_b4dfc0dbab472345 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMCNTEN ← (( do (pure (_get_HDFGWTR_EL2_Type_PMCNTEN (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMCNTEN == 1#1)) : Bool)
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
                                      else (PMCNTENCLR_write (Mk_PMCNTENCLR_Type (← (R_read t)))))))))))))
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
                              else (PMCNTENCLR_write (Mk_PMCNTENCLR_Type (← (R_read t))))))))))
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
                  else (PMCNTENCLR_write (Mk_PMCNTENCLR_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMCNTENCLR_write (Mk_PMCNTENCLR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCNTENSET_SysRegWrite32_8b1fd246c8987e40 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMCNTEN ← (( do (pure (_get_HDFGWTR_EL2_Type_PMCNTEN (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMCNTEN == 1#1)) : Bool)
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
                                      else (PMCNTENSET_write (Mk_PMCNTENSET_Type (← (R_read t)))))))))))))
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
                              else (PMCNTENSET_write (Mk_PMCNTENSET_Type (← (R_read t))))))))))
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
                  else (PMCNTENSET_write (Mk_PMCNTENSET_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMCNTENSET_write (Mk_PMCNTENSET_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMCR_SysRegWrite32_ed58155cb22a3fd6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T9 ← (( do (pure (_get_HSTR_EL2_Type_T9 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T9 ← (( do (pure (_get_HSTR_Type_T9 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMCR_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMCR_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPM ← (( do (pure (_get_MDCR_EL2_Type_TPM (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TPMCR ← (( do (pure (_get_MDCR_EL2_Type_TPMCR (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TPM ← (( do (pure (_get_HDCR_Type_TPM (← (HDCR_read ())))) ) : SailM (BitVec 1) )
  let __HDCR_TPMCR ← (( do (pure (_get_HDCR_Type_TPMCR (← (HDCR_read ())))) ) : SailM (BitVec 1) )
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
                 (pure (((_get_PMUSERENR_EL0_Type_UEN (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) != 0b01#2))) <||> (do
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
                                   (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGWTR_EL2_PMCR_EL0 == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPM == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPMCR == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HDCR_TPMCR == 1#1)) : Bool)
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
                                              else (__set_PMCR (Mk_PMCR_Type (← (R_read t)))))))))))))))
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TPMCR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HDCR_TPM == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HDCR_TPMCR == 1#1)) : Bool)
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
                                      else (__set_PMCR (Mk_PMCR_Type (← (R_read t))))))))))))
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
                  else (__set_PMCR (Mk_PMCR_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (__set_PMCR (Mk_PMCR_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_1402236c25c3ee30 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 3 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 3 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 3 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 3 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_1b282b60cc4c6447 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 20 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 20 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 20 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 20 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_272a6440ad5e9b96 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 13 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 13 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 13 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 13 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_379354bb12604d68 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (pure (10 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVCNTR_set 10 (← (R_read t)))))))))))
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
                           (pure (10 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVCNTR_set 10 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 10 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 10 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_3c9cffad5c0f5aa1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 11 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 11 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 11 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 11 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_3f499998ad4dfc7e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 19 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 19 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 19 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 19 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_659a321a15f83618 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 21 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 21 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 21 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 21 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_65d523b551bc8ca5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (pure (29 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVCNTR_set 29 (← (R_read t)))))))))))
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
                           (pure (29 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVCNTR_set 29 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 29 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 29 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_731843d10cb3a6ff (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (pure (15 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVCNTR_set 15 (← (R_read t)))))))))))
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
                           (pure (15 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVCNTR_set 15 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 15 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 15 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_77aaca2b0146bfed (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 0 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 0 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 0 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 0 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_77f99f1f07c86e99 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 4 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 4 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 4 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 4 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_7b729c1912b85359 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 30 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 30 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 30 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 30 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_7ee2623ac7e31637 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 16 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 16 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 16 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 16 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_80d48f0ea7518cab (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (pure (8 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVCNTR_set 8 (← (R_read t)))))))))))
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
                           (pure (8 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVCNTR_set 8 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 8 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 8 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_85d8fbb3220badc7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 7 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 7 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 7 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 7 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_8cf807c9cfa50ec9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (pure (26 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVCNTR_set 26 (← (R_read t)))))))))))
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
                           (pure (26 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVCNTR_set 26 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 26 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 26 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_91fa7b9aaafbca9c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 1 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 1 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 1 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 1 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_93be8ea1078adab4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 22 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 22 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 22 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 22 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_9aa0227f42759948 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (pure (12 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVCNTR_set 12 (← (R_read t)))))))))))
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
                           (pure (12 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVCNTR_set 12 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 12 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 12 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_9d177fd83b74425d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 2 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 2 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 2 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 2 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_9dd8faac045ac370 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 25 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 25 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 25 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 25 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_a333b5034a3b86cb (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 28 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 28 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 28 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 28 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_aaa5edab79dc57c7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 5 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 5 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 5 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 5 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_ae28080fa13bf9dd (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (pure (6 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVCNTR_set 6 (← (R_read t)))))))))))
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
                           (pure (6 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVCNTR_set 6 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 6 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 6 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_b7abf79765976a11 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 23 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 23 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 23 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 23 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_cdcaf594688625d5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 24 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 24 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 24 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 24 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_dabf302752d231bf (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (pure (9 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVCNTR_set 9 (← (R_read t)))))))))))
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
                           (pure (9 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVCNTR_set 9 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 9 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 9 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_e55f104293c82cc7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 17 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 17 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 17 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 17 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_e848e1982619415c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                   (pure (27 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVCNTR_set 27 (← (R_read t)))))))))))
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
                           (pure (27 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVCNTR_set 27 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 27 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 27 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_ea82053afec3aa68 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 18 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 18 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 18 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 18 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVCNTR_SysRegWrite32_f95277b9a9856b04 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TPM ← (( do (pure (_get_MDCR_EL3_Type_TPM (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EL0_EN ← (( do (pure (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __PMUSERENR_EN ← (( do (pure (_get_PMUSERENR_Type_EN (← (PMUSERENR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_TGE ← (( do (pure (_get_HCR_Type_TGE (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 ← (( do (pure (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (← readReg HDFGWTR_EL2))) ) : SailM (BitVec 1) )
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
                                  else (PMEVCNTR_set 14 (← (R_read t)))))))))))
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
                          else (PMEVCNTR_set 14 (← (R_read t))))))))
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
                  else (PMEVCNTR_set 14 (← (R_read t)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVCNTR_set 14 (← (R_read t)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_0dcdf6f29f657a14 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                   (pure (26 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVTYPER_set 26 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                           (pure (26 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVTYPER_set 26 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 26 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 26 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_11835dd6069bfdf3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                   (pure (9 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVTYPER_set 9 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                           (pure (9 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVTYPER_set 9 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 9 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 9 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_1340de29f3c858ee (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                   (pure (29 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVTYPER_set 29 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                           (pure (29 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVTYPER_set 29 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 29 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 29 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_172e7a30c1ece78a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                  else (PMEVTYPER_set 0 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                          else (PMEVTYPER_set 0 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 0 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 0 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_1acb3b092d3b80ff (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                  else (PMEVTYPER_set 20 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                          else (PMEVTYPER_set 20 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 20 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 20 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_1c8ef4dc87b91a11 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                   (pure (15 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVTYPER_set 15 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                           (pure (15 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVTYPER_set 15 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 15 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 15 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_225a412cd5799c58 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                   (pure (6 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVTYPER_set 6 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                           (pure (6 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVTYPER_set 6 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 6 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 6 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_2577251aa43d9dc4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                   (pure (8 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVTYPER_set 8 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                           (pure (8 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVTYPER_set 8 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 8 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 8 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_30cfe1e62bad0f9c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                   (pure (27 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVTYPER_set 27 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                           (pure (27 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVTYPER_set 27 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 27 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 27 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_3330ec8a9fad7b9b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                   (pure (10 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVTYPER_set 10 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                           (pure (10 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVTYPER_set 10 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 10 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 10 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_3e4eb9eb36921364 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                  else (PMEVTYPER_set 4 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                          else (PMEVTYPER_set 4 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 4 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 4 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_3fdce9a0d75c4d7a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                  else (PMEVTYPER_set 13 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                          else (PMEVTYPER_set 13 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 13 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 13 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def PMEVTYPER_SysRegWrite32_4034283bec67f894 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                   (pure (12 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                                  else (PMEVTYPER_set 12 (Mk_PMEVTYPER_Type (← (R_read t))))))))))))
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
                           (pure (12 ≥b (← (AArch32_GetNumEventCountersAccessible ()))))))) : Bool)
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
                          else (PMEVTYPER_set 12 (Mk_PMEVTYPER_Type (← (R_read t)))))))))
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
                  else (PMEVTYPER_set 12 (Mk_PMEVTYPER_Type (← (R_read t))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (PMEVTYPER_set 12 (Mk_PMEVTYPER_Type (← (R_read t))))
              else (pure ()))))


