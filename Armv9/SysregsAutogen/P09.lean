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
def DBGBXVR_SysRegRead32_f467d6fedc917b46 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              else (R_set t (← (DBGBXVR_read 3))))))))
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
                          else (R_set t (← (DBGBXVR_read 3))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 3))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBXVR_SysRegRead32_fa2068509c645345 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              else (R_set t (← (DBGBXVR_read 12))))))))
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
                          else (R_set t (← (DBGBXVR_read 12))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (← (DBGBXVR_read 12))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGCLAIMCLR_SysRegRead32_42a543613e49cb33 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (__get_DBGCLAIMCLR (← (DBGCLAIMCLR_read ()))))))))
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
                  else (R_set t (__get_DBGCLAIMCLR (← (DBGCLAIMCLR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DBGCLAIMCLR (← (DBGCLAIMCLR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGCLAIMSET_SysRegRead32_06784b0343d7d2f1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (__get_DBGCLAIMSET (← (DBGCLAIMSET_read ()))))))))
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
                  else (R_set t (__get_DBGCLAIMSET (← (DBGCLAIMSET_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DBGCLAIMSET (← (DBGCLAIMSET_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGDCCINT_SysRegRead32_ba602311e159b54c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SDCR_TDCC ← (( do (pure (_get_SDCR_Type_TDCC (← readReg SDCR))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TDCC ← (( do (pure (_get_HDCR_Type_TDCC (← (HDCR_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((Halted ()) <&&> (do
           (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
      then (R_set t (__get_DBGDCCINT (← (DBGDCCINT_read ()))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
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
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch32_TakeMonitorTrapException ()))
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
                                                  else (R_set t (__get_DBGDCCINT (← (DBGDCCINT_read ()))))))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                             (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch32_TakeMonitorTrapException ()))
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
                                      else (R_set t (__get_DBGDCCINT (← (DBGDCCINT_read ()))))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((__PSTATE_M != M32_Monitor) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeMonitorTrapException ())
                      else (R_set t (__get_DBGDCCINT (← (DBGDCCINT_read ())))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGDEVID1_SysRegRead32_faeb62347ce88c7a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (__get_DBGDEVID1 (← readReg DBGDEVID1)))))))
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
                  else (R_set t (__get_DBGDEVID1 (← readReg DBGDEVID1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DBGDEVID1 (← readReg DBGDEVID1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGDEVID2_SysRegRead32_6baefcc664f89312 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (__get_DBGDEVID2 (← readReg DBGDEVID2)))))))
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
                  else (R_set t (__get_DBGDEVID2 (← readReg DBGDEVID2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DBGDEVID2 (← readReg DBGDEVID2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGDEVID_SysRegRead32_66290830e754b76a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (← readReg DBGDEVID))))))
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
                  else (R_set t (← readReg DBGDEVID))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← readReg DBGDEVID))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGDIDR_SysRegRead32_8ee636612218bdd3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __DBGDSCRext_UDCCdis ← (( do (pure (_get_DBGDSCRext_Type_UDCCdis (← (DBGDSCRext_read ())))) ) : SailM (BitVec 1) )
  if ((←((Halted ()) <&&> (do
       (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
  then (R_set t (__get_DBGDIDR (← readReg DBGDIDR)))
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__DBGDSCRext_UDCCdis == 1#1)) : Bool)
                  then
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
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
                             (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2)))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)) <&&> (do
                               (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1)) <||> (do
                                 (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2)))))) : Bool)
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
                              else (R_set t (__get_DBGDIDR (← readReg DBGDIDR)))))))))
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
                          else (R_set t (__get_DBGDIDR (← readReg DBGDIDR)))))))
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
                      else (R_set t (__get_DBGDIDR (← readReg DBGDIDR)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (__get_DBGDIDR (← readReg DBGDIDR)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGDRAR_SysRegRead32_421a9884bf20a229 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __DBGDSCRext_UDCCdis ← (( do (pure (_get_DBGDSCRext_Type_UDCCdis (← (DBGDSCRext_read ())))) ) : SailM (BitVec 1) )
  if ((←((Halted ()) <&&> (do
       (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
  then (R_set t (Sail.BitVec.extractLsb (__get_DBGDRAR (← (DBGDRAR_read ()))) 31 0))
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__DBGDSCRext_UDCCdis == 1#1)) : Bool)
                  then
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
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
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)) <&&> (do
                               (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1)) <||> (do
                                 (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDRA (← (HDCR_read ())))) != 0b00#2)))))) : Bool)
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
                              else (R_set t (Sail.BitVec.extractLsb (__get_DBGDRAR (← (DBGDRAR_read ()))) 31 0))))))))
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDRA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
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
                          else (R_set t (Sail.BitVec.extractLsb (__get_DBGDRAR (← (DBGDRAR_read ()))) 31 0))))))
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
                      else (R_set t (Sail.BitVec.extractLsb (__get_DBGDRAR (← (DBGDRAR_read ()))) 31 0))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (Sail.BitVec.extractLsb (__get_DBGDRAR (← (DBGDRAR_read ()))) 31 0))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGDSAR_SysRegRead32_94ff484a75802dcb (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __DBGDSCRext_UDCCdis ← (( do (pure (_get_DBGDSCRext_Type_UDCCdis (← (DBGDSCRext_read ())))) ) : SailM (BitVec 1) )
  if ((←((Halted ()) <&&> (do
       (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
  then (R_set t (Sail.BitVec.extractLsb (__get_DBGDSAR (← readReg DBGDSAR)) 31 0))
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8)))
              else
                (do
                  if (((← (ELUsingAArch32 EL1)) && (__DBGDSCRext_UDCCdis == 1#1)) : Bool)
                  then
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
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
                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (ELUsingAArch32 EL2)) <&&> (do
                               (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1)) <||> (do
                                 (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDRA (← (HDCR_read ())))) != 0b00#2)))))) : Bool)
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
                              else (R_set t (Sail.BitVec.extractLsb (__get_DBGDSAR (← readReg DBGDSAR)) 31 0))))))))
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDRA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
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
                          else (R_set t (Sail.BitVec.extractLsb (__get_DBGDSAR (← readReg DBGDSAR)) 31 0))))))
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
                      else (R_set t (Sail.BitVec.extractLsb (__get_DBGDSAR (← readReg DBGDSAR)) 31 0))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (R_set t (Sail.BitVec.extractLsb (__get_DBGDSAR (← readReg DBGDSAR)) 31 0))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGDSCRext_SysRegRead32_bbe7b972eea0caec (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (__get_DBGDSCRext (← (DBGDSCRext_read ()))))))))
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
                  else (R_set t (__get_DBGDSCRext (← (DBGDSCRext_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DBGDSCRext (← (DBGDSCRext_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGDSCRint_SysRegRead32_4d6240b644e5e8d8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SDCR_TDCC ← (( do (pure (_get_SDCR_Type_TDCC (← readReg SDCR))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __DBGDSCRext_UDCCdis ← (( do (pure (_get_DBGDSCRext_Type_UDCCdis (← (DBGDSCRext_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TDCC ← (( do (pure (_get_HDCR_Type_TDCC (← (HDCR_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  if ((←((Halted ()) <&&> (do
       (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
  then
    (do
      if ((t == 15) : Bool)
      then
        (do
          let split_vec ← do (pure (Sail.BitVec.extractLsb (← (DBGDSCRint_read ())) 31 28))
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
      else (R_set t (__get_DBGDSCRint (← (DBGDSCRint_read ())))))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                          else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((← (ELUsingAArch32 EL1)) && (__DBGDSCRext_UDCCdis == 1#1)) : Bool)
                          then
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                   (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
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
                              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                              else
                                (do
                                  if (((←((EL2Enabled ()) <&&> (do
                                         (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                                  else
                                    (do
                                      if ((←((EL2Enabled ()) <&&> (do
                                           (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                                           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do
                                             (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2)))))) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                                      else
                                        (do
                                          if ((←((EL2Enabled ()) <&&> (do
                                               (ELUsingAArch32 EL2)) <&&> (do
                                               (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1)) <||> (do
                                                 (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2)))))) : Bool)
                                          then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                                              else
                                                (do
                                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                                  then
                                                    (do
                                                      if ((←((Halted ()) <&&> (do
                                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                      else (AArch32_TakeMonitorTrapException ()))
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
                                                          if ((t == 15) : Bool)
                                                          then
                                                            (do
                                                              let split_vec ← do (pure (Sail.BitVec.extractLsb (← (DBGDSCRint_read ())) 31 28))
                                                              writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
                                                              writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
                                                              writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
                                                              writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
                                                          else (R_set t (__get_DBGDSCRint (← (DBGDSCRint_read ())))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
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
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch32_TakeMonitorTrapException ()))
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
                                                      if ((t == 15) : Bool)
                                                      then
                                                        (do
                                                          let split_vec ← do (pure (Sail.BitVec.extractLsb (← (DBGDSCRint_read ())) 31 28))
                                                          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
                                                          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
                                                          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
                                                          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
                                                      else (R_set t (__get_DBGDSCRint (← (DBGDSCRint_read ())))))))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                             (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch32_TakeMonitorTrapException ()))
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
                                          if ((t == 15) : Bool)
                                          then
                                            (do
                                              let split_vec ← do (pure (Sail.BitVec.extractLsb (← (DBGDSCRint_read ())) 31 28))
                                              writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
                                              writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
                                              writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
                                              writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
                                          else (R_set t (__get_DBGDSCRint (← (DBGDSCRint_read ())))))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((__PSTATE_M != M32_Monitor) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeMonitorTrapException ())
                      else
                        (do
                          if ((t == 15) : Bool)
                          then
                            (do
                              let split_vec ← do (pure (Sail.BitVec.extractLsb (← (DBGDSCRint_read ())) 31 28))
                              writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
                              writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
                              writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
                              writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
                          else (R_set t (__get_DBGDSCRint (← (DBGDSCRint_read ()))))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGDTRRXext_SysRegRead32_4782be13f891eb2e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SDCR_TDCC ← (( do (pure (_get_SDCR_Type_TDCC (← readReg SDCR))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TDCC ← (( do (pure (_get_HDCR_Type_TDCC (← (HDCR_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((Halted ()) <&&> (do
           (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
      then (R_set t (← (DBGDTRRXext_read ())))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
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
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch32_TakeMonitorTrapException ()))
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
                                                  else (R_set t (← (DBGDTRRXext_read ())))))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                             (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch32_TakeMonitorTrapException ()))
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
                                      else (R_set t (← (DBGDTRRXext_read ())))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((__PSTATE_M != M32_Monitor) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeMonitorTrapException ())
                      else (R_set t (← (DBGDTRRXext_read ()))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGDTRRXint_SysRegRead32_ce20085c05aae144 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  then (R_set t (← (DBGDTRRXint_read ())))
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
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
              else (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8)))
          else
            (do
              if (((← (ELUsingAArch32 EL1)) && (__DBGDSCRext_UDCCdis == 1#1)) : Bool)
              then
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
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
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                               (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do
                                 (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2)))))) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                          else
                            (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (ELUsingAArch32 EL2)) <&&> (do
                                   (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1)) <||> (do
                                     (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2)))))) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                                  then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                      then (AArch32_TakeMonitorTrapException ())
                                      else
                                        (do
                                          if (((←((pure (HaveEL EL3)) <&&> (do
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                          then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))
                                          else (R_set t (← (DBGDTRRXint_read ()))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
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
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                  then (AArch32_TakeMonitorTrapException ())
                                  else
                                    (do
                                      if (((←((pure (HaveEL EL3)) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                      then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))
                                      else (R_set t (← (DBGDTRRXint_read ()))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeMonitorTrapException ())
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))
                          else (R_set t (← (DBGDTRRXint_read ()))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((__PSTATE_M != M32_Monitor) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeMonitorTrapException ())
                      else (R_set t (← (DBGDTRRXint_read ()))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGDTRTXext_SysRegRead32_dbe218a3250d179f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SDCR_TDCC ← (( do (pure (_get_SDCR_Type_TDCC (← readReg SDCR))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TDCC ← (( do (pure (_get_HDCR_Type_TDCC (← (HDCR_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((Halted ()) <&&> (do
           (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG)))) : Bool)
      then (R_set t (← (DBGDTRTXext_read ())))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((EL2Enabled ()) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HDCR_TDCC == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
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
                                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                                          then
                                            (do
                                              if ((←((Halted ()) <&&> (do
                                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                                          else
                                            (do
                                              if (((←((pure (HaveEL EL3)) <&&> (do
                                                     (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                              then
                                                (do
                                                  if ((←((Halted ()) <&&> (do
                                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                  else (AArch32_TakeMonitorTrapException ()))
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
                                                  else (R_set t (← (DBGDTRTXext_read ())))))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                             (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                             (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else
                        (do
                          if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                                 (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then
                                (do
                                  if ((←((Halted ()) <&&> (do
                                       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (ELUsingAArch32 EL3)))) && (__SDCR_TDCC == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch32_TakeMonitorTrapException ()))
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
                                      else (R_set t (← (DBGDTRTXext_read ())))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((__PSTATE_M != M32_Monitor) && (__SDCR_TDCC == 1#1)) : Bool)
                      then (AArch32_TakeMonitorTrapException ())
                      else (R_set t (← (DBGDTRTXext_read ()))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGOSDLR_SysRegRead32_c1e6447a93f7efb4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL2_TDOSA ← (( do (pure (_get_MDCR_EL2_Type_TDOSA (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __HDCR_TDOSA ← (( do (pure (_get_HDCR_Type_TDOSA (← (HDCR_read ())))) ) : SailM (BitVec 1) )
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
               (pure ((_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3)) == 1#1))) <&&> (do
               (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                 (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA"))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                   (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDOSA (← readReg MDCR_EL2))) != 0b00#2))) <&&> (do
                   (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                     (__IMPDEF_boolean "Trapped by MDCR_EL2.TDOSA"))))) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (ELUsingAArch32 EL2)) <&&> (do
                       (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDOSA (← (HDCR_read ())))) != 0b00#2))) <&&> (do
                       (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                         (__IMPDEF_boolean "Trapped by HDCR.TDOSA"))))) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((pure (HaveEL EL3)) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                           (pure ((_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3)) == 1#1))) <&&> (do
                           (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                             (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA"))))) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else (R_set t (← (__get_DBGOSDLR (← (DBGOSDLR_read ())))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                   (pure ((_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3)) == 1#1))) <&&> (do
                   (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                     (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA"))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((pure (HaveEL EL3)) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                       (pure ((_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3)) == 1#1))) <&&> (do
                       (IsFeatureImplemented FEAT_DoubleLock) <||> (do
                         (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA"))))) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                  else (R_set t (← (__get_DBGOSDLR (← (DBGOSDLR_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (← (__get_DBGOSDLR (← (DBGOSDLR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGOSECCR_SysRegRead32_391dd35ddd37f699 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __DBGOSLSR_OSLK ← (( do (pure (_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ())))) ) : SailM (BitVec 1) )
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
                          if ((__DBGOSLSR_OSLK == 0#1) : Bool)
                          then (R_set t (← (__UNKNOWN_bits 32)))
                          else (R_set t (← (DBGOSECCR_read ()))))))))
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
                      if ((__DBGOSLSR_OSLK == 0#1) : Bool)
                      then (R_set t (← (__UNKNOWN_bits 32)))
                      else (R_set t (← (DBGOSECCR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__DBGOSLSR_OSLK == 0#1) : Bool)
                  then (R_set t (← (__UNKNOWN_bits 32)))
                  else (R_set t (← (DBGOSECCR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGOSLSR_SysRegRead32_7c8a1f5e56c0fe64 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDOSA ← (( do (pure (_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                   (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDOSA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (ELUsingAArch32 EL2)) <&&> (do
                       (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDOSA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else (R_set t (__get_DBGOSLSR (← (DBGOSLSR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                  else (R_set t (__get_DBGOSLSR (← (DBGOSLSR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DBGOSLSR (← (DBGOSLSR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGPRCR_SysRegRead32_ff2c6b0471b55490 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDOSA ← (( do (pure (_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                   (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDOSA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
              then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (ELUsingAArch32 EL2)) <&&> (do
                       (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDOSA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                  then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else (R_set t (__get_DBGPRCR (← (DBGPRCR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDOSA == 1#1)) : Bool)
                  then
                    (do
                      if ((←((Halted ()) <&&> (do
                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                  else (R_set t (__get_DBGPRCR (← (DBGPRCR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DBGPRCR (← (DBGPRCR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGVCR_SysRegRead32_19db55a72a941c5f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (__get_DBGVCR (← (DBGVCR_read ()))))))))
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
                  else (R_set t (__get_DBGVCR (← (DBGVCR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DBGVCR (← (DBGVCR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_2c8e3f6807d0cbe3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((9 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 9)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 9)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 9)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_34b30f3cf3218c16 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((11 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 11)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 11)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 11)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_3b1b0be7aff03388 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((14 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 14)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 14)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 14)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_427272e014730b50 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((6 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 6)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 6)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 6)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_60f3efc31648e354 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((12 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 12)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 12)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 12)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_696fee9dbbdf30bb (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((5 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 5)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 5)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 5)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_862efdc01d71fc1c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((3 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 3)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 3)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 3)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_a166e9fb14e381a7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((0 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 0)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 0)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 0)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_c04d3d89801ab85d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((2 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 2)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 2)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 2)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_c11448c554efe1b1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((4 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 4)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 4)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 4)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_c49e6cc415f000b3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((7 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 7)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 7)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 7)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_c5e0186238203543 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((10 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 10)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 10)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 10)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_e262457611dfe741 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((1 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 1)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 1)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 1)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_f40826807efdc23f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((8 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 8)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 8)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 8)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_fa67eb6a8f2349c1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((15 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 15)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 15)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 15)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegRead32_fba46a7399a2c310 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((13 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWCR (← (DBGWCR_read 13)))))))))
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
                          else (R_set t (__get_DBGWCR (← (DBGWCR_read 13)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWCR (← (DBGWCR_read 13)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWFAR_SysRegRead32_eb3aaa02963f85c2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (__get_DBGWFAR (← readReg DBGWFAR)))))))
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
                  else (R_set t (__get_DBGWFAR (← readReg DBGWFAR)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DBGWFAR (← readReg DBGWFAR)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_00161ecd371e1b48 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((9 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 9)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 9)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 9)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_0f5b4c975d3928f0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((8 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 8)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 8)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 8)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_2e5f3331ba566316 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((12 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 12)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 12)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 12)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_328f6a9c09b12c20 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((3 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 3)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 3)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 3)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_4bb9af81a75faa61 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((7 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 7)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 7)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 7)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_4f5bca529a325f7f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((6 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 6)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 6)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 6)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_672b3a4673cc16b1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((11 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 11)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 11)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 11)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_6a1d08c571006557 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((1 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 1)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 1)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 1)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_7cd7645018d2576e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((2 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 2)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 2)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 2)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_9fd65afd85a62538 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((13 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 13)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 13)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 13)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_a8d1c2ea29be76f1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((10 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 10)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 10)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 10)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_b4df3a7002c9f7a0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((14 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 14)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 14)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 14)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_c6ca5289ed10ec19 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((0 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 0)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 0)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 0)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_da9f18e2f273c366 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((4 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 4)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 4)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 4)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_de66eaaa5ee8659b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((15 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 15)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 15)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 15)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegRead32_f5ed12ff92151086 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((5 ≥b (← readReg NUM_WATCHPOINTS)) : Bool)
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
                              else (R_set t (__get_DBGWVR (← (DBGWVR_read 5)))))))))
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
                          else (R_set t (__get_DBGWVR (← (DBGWVR_read 5)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (R_set t (__get_DBGWVR (← (DBGWVR_read 5)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DFAR_SysRegRead32_24eaaed98bd8c8b9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T6 ← (( do (pure (_get_HSTR_EL2_Type_T6 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T6 ← (( do (pure (_get_HSTR_Type_T6 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
                          then (R_set t (← (DFAR_NS_read ())))
                          else (R_set t (← (DFAR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (DFAR_NS_read ())))
              else (R_set t (← (DFAR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← (DFAR_S_read ())))
                  else (R_set t (← (DFAR_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DFSR_SysRegRead32_094c65de67978ba7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          then (R_set t (← (DFSR_NS_read ())))
                          else (R_set t (← (DFSR_read ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure (HaveEL EL3)) <&&> (do
                   (ELUsingAArch32 EL3)))) : Bool)
              then (R_set t (← (DFSR_NS_read ())))
              else (R_set t (← (DFSR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (R_set t (← readReg DFSR_S))
                  else (R_set t (← (DFSR_NS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DISR_SysRegRead32_9f42ad0cc10a5f19 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_AMO ← (( do (pure (_get_HCR_EL2_Type_AMO (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_AMO ← (( do (pure (_get_HCR_Type_AMO (← (HCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EA ← (( do (pure (_get_SCR_EL3_Type_EA (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EA ← (( do (pure (_get_SCR_Type_EA (← readReg SCR))) ) : SailM (BitVec 1) )
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
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_AMO == 1#1)) : Bool)
                  then (R_set t (Sail.BitVec.extractLsb (__get_VDISR_EL2 (← readReg VDISR_EL2)) 31 0))
                  else
                    (do
                      if (((←((EL2Enabled ()) <&&> (do
                             (ELUsingAArch32 EL2)))) && (__HCR_AMO == 1#1)) : Bool)
                      then (R_set t (__get_VDISR (← (VDISR_read ()))))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                                 (pure (! (← (Halted ()))))))) && (__SCR_EL3_EA == 1#1)) : Bool)
                          then (R_set t (Zeros (n := 32)))
                          else
                            (do
                              if (((←((pure (HaveEL EL3)) <&&> (do
                                     (ELUsingAArch32 EL3)) <&&> (do
                                     (pure (! (← (Halted ()))))))) && (__SCR_EA == 1#1)) : Bool)
                              then (R_set t (Zeros (n := 32)))
                              else (R_set t (__get_DISR (← (DISR_read ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (HaveEL EL3)) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))) <&&> (do
                     (pure (! (← (Halted ()))))))) && (__SCR_EL3_EA == 1#1)) : Bool)
              then (R_set t (Zeros (n := 32)))
              else
                (do
                  if (((←((pure (HaveEL EL3)) <&&> (do
                         (ELUsingAArch32 EL3)) <&&> (do
                         (pure (! (← (Halted ()))))))) && (__SCR_EA == 1#1)) : Bool)
                  then (R_set t (Zeros (n := 32)))
                  else (R_set t (__get_DISR (← (DISR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_DISR (← (DISR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DLR_SysRegRead32_8fb9614c85c3b992 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (R_set t (← (DLR_read ())))

/-- Type quantifiers: t : Int -/
def DSPSR2_SysRegRead32_6da9b04f72c6c3f2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (R_set t (__get_DSPSR2 (← (DSPSR2_read ()))))

/-- Type quantifiers: t : Int -/
def DSPSR_SysRegRead32_b8ab5544c94609ec (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (R_set t (← (DSPSR_read ())))

/-- Type quantifiers: t : Int -/
def ERRIDR_SysRegRead32_98e51b40bf051290 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (__get_ERRIDR (← (ERRIDR_read ()))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (__get_ERRIDR (← (ERRIDR_read ()))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (__get_ERRIDR (← (ERRIDR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERRSELR_SysRegRead32_89386228f05f3e86 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (__get_ERRSELR (← (ERRSELR_read ()))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (__get_ERRSELR (← (ERRSELR_read ()))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (__get_ERRSELR (← (ERRSELR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXADDR2_SysRegRead32_ee8844bbda44b8b3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXADDR2_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXADDR2_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXADDR2_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXADDR_SysRegRead32_ca0ccd8f0f00724b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXADDR_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXADDR_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXADDR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXCTLR2_SysRegRead32_538545d1d2bef52f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXCTLR2_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXCTLR2_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXCTLR2_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXCTLR_SysRegRead32_223464c9a84e4bc3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXCTLR_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXCTLR_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXCTLR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXFR2_SysRegRead32_2ed16754dcca71f1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXFR2_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXFR2_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXFR2_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXFR_SysRegRead32_38334a5a99e8eedf (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXFR_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXFR_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXFR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC0_SysRegRead32_945d1e7792b59484 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXMISC0_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXMISC0_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXMISC0_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC1_SysRegRead32_24c39414a2e1d0b1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXMISC1_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXMISC1_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXMISC1_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC2_SysRegRead32_17926cb7ab87a983 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXMISC2_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXMISC2_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXMISC2_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC3_SysRegRead32_2387d2346ca52482 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXMISC3_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXMISC3_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXMISC3_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC4_SysRegRead32_6139ba68e2078794 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXMISC4_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXMISC4_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXMISC4_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC5_SysRegRead32_e7e0b0e38858a927 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXMISC5_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXMISC5_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXMISC5_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC6_SysRegRead32_9abf31f5358e2067 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXMISC6_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXMISC6_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXMISC6_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXMISC7_SysRegRead32_99b78145ea2ea108 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXMISC7_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXMISC7_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXMISC7_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ERXSTATUS_SysRegRead32_5466a91990979d70 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_TERR ← (( do (pure (_get_SCR_EL3_Type_TERR (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_TERR ← (( do (pure (_get_SCR_Type_TERR (← readReg SCR))) ) : SailM (BitVec 1) )
  let __HSTR_EL2_T5 ← (( do (pure (_get_HSTR_EL2_Type_T5 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T5 ← (( do (pure (_get_HSTR_Type_T5 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TERR ← (( do (pure (_get_HCR_EL2_Type_TERR (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR2_TERR ← (( do (pure (_get_HCR2_Type_TERR (← (HCR2_read ())))) ) : SailM (BitVec 1) )
  let __PSTATE_M ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
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
                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
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
                                 (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_TERR == 1#1)) : Bool)
                          then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
                          else
                            (do
                              if (((←((EL2Enabled ()) <&&> (do
                                     (ELUsingAArch32 EL2)))) && (__HCR2_TERR == 1#1)) : Bool)
                              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
                              else
                                (do
                                  if (((←((pure (HaveEL EL3)) <&&> (do
                                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                                  then
                                    (do
                                      if ((←((Halted ()) <&&> (do
                                           (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      if ((((←((pure (HaveEL EL3)) <&&> (do
                                               (ELUsingAArch32 EL3)))) && (__PSTATE_M != M32_Monitor)) && (__SCR_TERR == 1#1)) : Bool)
                                      then
                                        (do
                                          if ((←((Halted ()) <&&> (do
                                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                          else (AArch32_TakeMonitorTrapException ()))
                                      else (R_set t (← (ERXSTATUS_read ())))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__SCR_EL3_TERR == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (ELUsingAArch32 EL3)))) && (__SCR_TERR == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch32_TakeMonitorTrapException ()))
                          else (R_set t (← (ERXSTATUS_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then (AArch32_TakeMonitorTrapException ())
                  else (R_set t (← (ERXSTATUS_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def FCSEIDR_SysRegRead32_cb9b2f57b39997f9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T13 ← (( do (pure (_get_HSTR_EL2_Type_T13 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T13 ← (( do (pure (_get_HSTR_Type_T13 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (R_set t (__get_FCSEIDR (← readReg FCSEIDR)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (__get_FCSEIDR (← readReg FCSEIDR)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (R_set t (__get_FCSEIDR (← readReg FCSEIDR)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HACR_SysRegRead32_a717d701accd9575 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HACR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HACR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HACTLR2_SysRegRead32_0445e99237541ba9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HACTLR2_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HACTLR2_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HACTLR_SysRegRead32_2bf8282054123267 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HACTLR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HACTLR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HADFSR_SysRegRead32_c586b2ce1fe8150f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (R_set t (← (HADFSR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HADFSR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HAIFSR_SysRegRead32_6fddec5e27f03691 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (R_set t (← (HAIFSR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HAIFSR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HAMAIR0_SysRegRead32_377efb316c773bdf (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T10 ← (( do (pure (_get_HSTR_EL2_Type_T10 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T10 ← (( do (pure (_get_HSTR_Type_T10 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HAMAIR0_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HAMAIR0_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HAMAIR1_SysRegRead32_b4da9627c11c58d9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T10 ← (( do (pure (_get_HSTR_EL2_Type_T10 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T10 ← (( do (pure (_get_HSTR_Type_T10 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HAMAIR1_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HAMAIR1_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HCPTR_SysRegRead32_36b5e5e38803084d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TCPAC ← (( do (pure (_get_CPTR_EL3_Type_TCPAC (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
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
                  else (R_set t (← (__get_HCPTR (← (HCPTR_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (__get_HCPTR (← (HCPTR_read ()))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HCR2_SysRegRead32_f7ed44285bae255b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HCR2_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HCR2_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HCR_SysRegRead32_9baa0bb29521adc6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HCR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HCR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HDCR_SysRegRead32_ca37580e50123c00 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
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
                      else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                  else (R_set t (__get_HDCR (← (HDCR_read ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_HDCR (← (HDCR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HDFAR_SysRegRead32_b442fa1081ced0da (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T6 ← (( do (pure (_get_HSTR_EL2_Type_T6 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T6 ← (( do (pure (_get_HSTR_Type_T6 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HDFAR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HDFAR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HIFAR_SysRegRead32_97075d5570b400a8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T6 ← (( do (pure (_get_HSTR_EL2_Type_T6 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T6 ← (( do (pure (_get_HSTR_Type_T6 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HIFAR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HIFAR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HMAIR0_SysRegRead32_f157e09e6f0e50a5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T10 ← (( do (pure (_get_HSTR_EL2_Type_T10 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T10 ← (( do (pure (_get_HSTR_Type_T10 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HMAIR0_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HMAIR0_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HMAIR1_SysRegRead32_fd5c958c2380e7ae (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T10 ← (( do (pure (_get_HSTR_EL2_Type_T10 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T10 ← (( do (pure (_get_HSTR_Type_T10 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HMAIR1_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HMAIR1_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HPFAR_SysRegRead32_985da2a8b12c2ec3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T6 ← (( do (pure (_get_HSTR_EL2_Type_T6 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T6 ← (( do (pure (_get_HSTR_Type_T6 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (__get_HPFAR (← (HPFAR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_HPFAR (← (HPFAR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HRMR_SysRegRead32_ce0678ac4cae9992 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  if (((←((pure ((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do (EL2Enabled ())))) && (IsHighestEL EL2))) <&&> (do
         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HSTR_EL2_T12 == 1#1)) : Bool)
  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))
  else
    (do
      if (((←((pure ((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do (EL2Enabled ())))) && (IsHighestEL EL2))) <&&> (do
             (ELUsingAArch32 EL2)))) && (__HSTR_T12 == 1#1)) : Bool)
      then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
      else
        (do
          if ((((← readReg PSTATE).EL == EL2) && (IsHighestEL EL2)) : Bool)
          then (R_set t (__get_HRMR (← (HRMR_read ()))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit)))

/-- Type quantifiers: t : Int -/
def HSCTLR_SysRegRead32_7d1999deb1c478b9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (__get_HSCTLR (← (HSCTLR_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (__get_HSCTLR (← (HSCTLR_read ()))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HSR_SysRegRead32_8b698f9bb5858477 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (R_set t (← (HSR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HSR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HSTR_SysRegRead32_1f7e6811bde077a5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (__get_HSTR (← (HSTR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_HSTR (← (HSTR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HTCR_SysRegRead32_ad0d0f0fabd96a9f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (R_set t (__get_HTCR (← (HTCR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_HTCR (← (HTCR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HTPIDR_SysRegRead32_882efba325cc7f8f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (R_set t (← (HTPIDR_read ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (HTPIDR_read ()))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HTRFCR_SysRegRead32_b1ffee03b0b71c5a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T1 ← (( do (pure (_get_HSTR_EL2_Type_T1 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T1 ← (( do (pure (_get_HSTR_Type_T1 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TTRF ← (( do (pure (_get_MDCR_EL3_Type_TTRF (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SDCR_TTRF ← (( do (pure (_get_SDCR_Type_TTRF (← readReg SDCR))) ) : SailM (BitVec 1) )
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
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
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
                          else (R_set t (__get_HTRFCR (← (HTRFCR_read ()))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_HTRFCR (← (HTRFCR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def HVBAR_SysRegRead32_d6c8aecebbe5fd70 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (R_set t (__get_HVBAR (← (HVBAR_read ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_HVBAR (← (HVBAR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_BPR0_SysRegRead32_7c3bac42de4de5ac (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      then (R_set t (__get_ICV_BPR0 (← (ICV_BPR0_read ()))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (R_set t (__get_ICV_BPR0 (← (ICV_BPR0_read ()))))
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
                                                  else (R_set t (__get_ICC_BPR0 (← (ICC_BPR0_read ())))))))))))))))
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
                              else (R_set t (__get_ICC_BPR0 (← (ICC_BPR0_read ())))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICC_BPR0 (← (ICC_BPR0_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_BPR1_SysRegRead32_afd3e126a3be69bd (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      then (R_set t (__get_ICV_BPR1 (← (ICV_BPR1_read ()))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                          then (R_set t (__get_ICV_BPR1 (← (ICV_BPR1_read ()))))
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
                                                      then (R_set t (__get_ICC_BPR1_NS (← (ICC_BPR1_NS_read ()))))
                                                      else (R_set t (__get_ICC_BPR1 (← (ICC_BPR1_read ()))))))))))))))))
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
                                  then (R_set t (__get_ICC_BPR1_NS (← (ICC_BPR1_NS_read ()))))
                                  else (R_set t (__get_ICC_BPR1 (← (ICC_BPR1_read ()))))))))))
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
                      then (R_set t (__get_ICC_BPR1_S (← (ICC_BPR1_S_read ()))))
                      else (R_set t (__get_ICC_BPR1_NS (← (ICC_BPR1_NS_read ()))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_HPPIR0_SysRegRead32_b32431f23ec6243a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      then (R_set t (__get_ICV_HPPIR0 (← (ICV_HPPIR0_read ()))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (R_set t (__get_ICV_HPPIR0 (← (ICV_HPPIR0_read ()))))
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
                                                  else (R_set t (__get_ICC_HPPIR0 (← (ICC_HPPIR0_read ())))))))))))))))
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
                              else (R_set t (__get_ICC_HPPIR0 (← (ICC_HPPIR0_read ())))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICC_HPPIR0 (← (ICC_HPPIR0_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_HSRE_SysRegRead32_0e6b0f816b017dd6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      else (R_set t (__get_ICC_HSRE (← (ICC_HSRE_read ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (← (EL2Enabled ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICC_HSRE (← (ICC_HSRE_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_IAR0_SysRegRead32_22d846d8001a81c5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      then (R_set t (__get_ICV_IAR0 (← (ICV_IAR0_read ()))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (R_set t (__get_ICV_IAR0 (← (ICV_IAR0_read ()))))
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
                                                  else (R_set t (__get_ICC_IAR0 (← (ICC_IAR0_read ())))))))))))))))
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
                              else (R_set t (__get_ICC_IAR0 (← (ICC_IAR0_read ())))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICC_IAR0 (← (ICC_IAR0_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_IAR1_SysRegRead32_8d514dfe4b6957fe (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      then (R_set t (__get_ICV_IAR1 (← (ICV_IAR1_read ()))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                          then (R_set t (__get_ICV_IAR1 (← (ICV_IAR1_read ()))))
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
                                                  else (R_set t (__get_ICC_IAR1 (← (ICC_IAR1_read ())))))))))))))))
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
                              else (R_set t (__get_ICC_IAR1 (← (ICC_IAR1_read ())))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICC_IAR1 (← (ICC_IAR1_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_MCTLR_SysRegRead32_f1e0f70708724584 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else (R_set t (__get_ICC_MCTLR (← readReg ICC_MCTLR))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_MGRPEN1_SysRegRead32_92bbab53b6030359 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  else (R_set t (__get_ICC_MGRPEN1 (← readReg ICC_MGRPEN1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_MSRE_SysRegRead32_79a8be5256989c32 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (R_set t (__get_ICC_MSRE (← readReg ICC_MSRE)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_PMR_SysRegRead32_aa604b328cea6616 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                  then (R_set t (__get_ICV_PMR (← (ICV_PMR_read ()))))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                      then (R_set t (__get_ICV_PMR (← (ICV_PMR_read ()))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (R_set t (__get_ICV_PMR (← (ICV_PMR_read ()))))
                                          else
                                            (do
                                              if (((←((EL2Enabled ()) <&&> (do
                                                     (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                              then (R_set t (__get_ICV_PMR (← (ICV_PMR_read ()))))
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
                                                      else (R_set t (__get_ICC_PMR (← (ICC_PMR_read ()))))))))))))))))
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
                              else (R_set t (__get_ICC_PMR (← (ICC_PMR_read ())))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICC_PMR (← (ICC_PMR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICC_SRE_SysRegRead32_4fd5ef8b1be9c965 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                          then (R_set t (__get_ICC_SRE_S (← (ICC_SRE_S_read ()))))
                                          else (R_set t (__get_ICC_SRE_NS (← (ICC_SRE_NS_read ())))))
                                      else (R_set t (__get_ICC_SRE (← (ICC_SRE_read ()))))))))))))
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
                              then (R_set t (__get_ICC_SRE_S (← (ICC_SRE_S_read ()))))
                              else (R_set t (__get_ICC_SRE_NS (← (ICC_SRE_NS_read ())))))
                          else (R_set t (__get_ICC_SRE (← (ICC_SRE_read ()))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then (R_set t (__get_ICC_SRE_S (← (ICC_SRE_S_read ()))))
                  else (R_set t (__get_ICC_SRE_NS (← (ICC_SRE_NS_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegRead32_8a9ae74c0d05c4d8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_AP0R_read 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_AP0R_read 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegRead32_941887291ce9d9ce (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegRead32_f7de8d51fc141ec6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegRead32_fa5d134ae7836c23 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegRead32_0df0cbf9f8197fd3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_AP1R_read 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_AP1R_read 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegRead32_19b0a11aa0aeb1f4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegRead32_21b1b518e28be46b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegRead32_893d03c9b3bc367a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HSTR_EL2_T12 ← (( do (pure (_get_HSTR_EL2_Type_T12 (← readReg HSTR_EL2))) ) : SailM (BitVec 1) )
  let __HSTR_T12 ← (( do (pure (_get_HSTR_Type_T12 (← (HSTR_read ())))) ) : SailM (BitVec 1) )
  let __ICC_HSRE_SRE ← (( do (pure (_get_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())))) ) : SailM (BitVec 1) )
  let __ICC_MSRE_SRE ← (( do (pure (_get_ICC_MSRE_Type_SRE (← readReg ICC_MSRE))) ) : SailM (BitVec 1) )
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: t : Int -/
def ICH_EISR_SysRegRead32_6c8baaadbfc73196 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_EISR (← (ICH_EISR_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_EISR (← (ICH_EISR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_ELRSR_SysRegRead32_1d9d4e5a379e315c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (Sail.BitVec.extractLsb (__get_ICH_ELRSR (← (ICH_ELRSR_read ()))) 31 0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (Sail.BitVec.extractLsb (__get_ICH_ELRSR (← (ICH_ELRSR_read ()))) 31 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_HCR_SysRegRead32_49d2eca523adf51c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_HCR (← (ICH_HCR_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_HCR (← (ICH_HCR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_1fc599a8419d7830 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 4)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 4)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_2d5fdc0c0df5489a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 13)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 13)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_2f30eacc54c36948 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 6)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 6)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_376ab6d5a4721697 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 5)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 5)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_5e3a0d745c54eaf7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 7)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 7)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_604585b24b60fdae (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 10)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 10)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_7819c0333582e456 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 15)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 15)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_792ff81aa718ff76 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 2)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_9d34a1da3a3d8af6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 11)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 11)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_a29c320b6a841a2d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 3)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 3)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_c7c19edd6493b5c7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 9)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 9)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_ce80e380eb49f8f4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 1)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_ebf1ecd69e0bcfb2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 8)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 8)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_ede8f5720388c87c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 14)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 14)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_fa7f4e2cc52b6a12 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LRC_SysRegRead32_ff6694005f1d0b3b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 12)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_LRC (← (ICH_LRC_read 12)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_074065db8610395b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 1))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_1acb03f084987252 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 13))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 13))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_1d190d8da488b71c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 14))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 14))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_1d761f8769ecc810 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 10))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 10))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_223cf2e0fdc1ff05 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_3bf5b46e983d4c12 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 9))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 9))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_3d583fbb8aa5513b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 7))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 7))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_3dfad36dd01cdeec (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 5))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 5))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_45c00df4516639fa (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 11))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 11))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_7cf030ba66b1e3f5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 6))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 6))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_8e77adbc9c8c8d7d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 15))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 15))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_91b224d16fef9888 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 4))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 4))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_9b173de940ca1870 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 8))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 8))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_aff6b82779d5a019 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_b53ec5837b358bc1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 3))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 3))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_LR_SysRegRead32_ca0e018c3a31cc4a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (← (ICH_LR_read 12))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICH_LR_read 12))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_MISR_SysRegRead32_b1b3df82fdb149c6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_MISR (← (ICH_MISR_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_MISR (← (ICH_MISR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_VMCR_SysRegRead32_c4afb8cb8e0d0a5d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_VMCR (← (ICH_VMCR_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_VMCR (← (ICH_VMCR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICH_VTR_SysRegRead32_1187208e70ad69e9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (R_set t (__get_ICH_VTR (← (ICH_VTR_read ())))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICH_VTR (← (ICH_VTR_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_AP0R_SysRegRead32_30ba9fd61ae1e604 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICV_AP0R_SysRegRead32_72af30ac5c792211 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      then (R_set t (← (ICV_AP0R_read 0)))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (R_set t (← (ICV_AP0R_read 0)))
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
                                                  else (R_set t (← (ICC_AP0R_read 0))))))))))))))
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
                              else (R_set t (← (ICC_AP0R_read 0))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (← (ICC_AP0R_read 0))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_AP0R_SysRegRead32_c3c1719656dd9c14 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICV_AP0R_SysRegRead32_dc4d5081c52e9718 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICV_AP1R_SysRegRead32_06c655ca9c8e2c1e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICV_AP1R_SysRegRead32_97b8eb46fd54eb2b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICV_AP1R_SysRegRead32_c631f0bb4000bb22 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
def ICV_AP1R_SysRegRead32_f50b3adcd6cb4d7f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      then (R_set t (← (ICV_AP1R_read 0)))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                          then (R_set t (← (ICV_AP1R_read 0)))
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
                                                      then (R_set t (← (ICC_AP1R_NS_read 0)))
                                                      else (R_set t (← (ICC_AP1R_read 0)))))))))))))))
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
                                  then (R_set t (← (ICC_AP1R_NS_read 0)))
                                  else (R_set t (← (ICC_AP1R_read 0)))))))))
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
                      then (R_set t (← (ICC_AP1R_S_read 0)))
                      else (R_set t (← (ICC_AP1R_NS_read 0)))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_CTLR_SysRegRead32_084685ae7c38b87e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                  then (R_set t (__get_ICV_CTLR (← (ICV_CTLR_read ()))))
                                  else
                                    (do
                                      if (((←((EL2Enabled ()) <&&> (do
                                             (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_IMO == 1#1)) : Bool)
                                      then (R_set t (__get_ICV_CTLR (← (ICV_CTLR_read ()))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (R_set t (__get_ICV_CTLR (← (ICV_CTLR_read ()))))
                                          else
                                            (do
                                              if (((←((EL2Enabled ()) <&&> (do
                                                     (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                              then (R_set t (__get_ICV_CTLR (← (ICV_CTLR_read ()))))
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
                                                          then (R_set t (__get_ICC_CTLR_NS (← (ICC_CTLR_NS_read ()))))
                                                          else (R_set t (__get_ICC_CTLR (← (ICC_CTLR_read ())))))))))))))))))
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
                                  then (R_set t (__get_ICC_CTLR_NS (← (ICC_CTLR_NS_read ()))))
                                  else (R_set t (__get_ICC_CTLR (← (ICC_CTLR_read ()))))))))))
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
                      then (R_set t (__get_ICC_CTLR_S (← (ICC_CTLR_S_read ()))))
                      else (R_set t (__get_ICC_CTLR_NS (← (ICC_CTLR_NS_read ()))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_HPPIR1_SysRegRead32_b45bf9d6297cda27 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      then (R_set t (__get_ICV_HPPIR1 (← (ICV_HPPIR1_read ()))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_IMO == 1#1)) : Bool)
                                          then (R_set t (__get_ICV_HPPIR1 (← (ICV_HPPIR1_read ()))))
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
                                                  else (R_set t (__get_ICC_HPPIR1 (← (ICC_HPPIR1_read ())))))))))))))))
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
                              else (R_set t (__get_ICC_HPPIR1 (← (ICC_HPPIR1_read ())))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICC_HPPIR1 (← (ICC_HPPIR1_read ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def ICV_IGRPEN0_SysRegRead32_762db4bb97023cca (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                      then (R_set t (__get_ICV_IGRPEN0 (← (ICV_IGRPEN0_read ()))))
                                      else
                                        (do
                                          if (((←((EL2Enabled ()) <&&> (do
                                                 (ELUsingAArch32 EL2)))) && (__HCR_FMO == 1#1)) : Bool)
                                          then (R_set t (__get_ICV_IGRPEN0 (← (ICV_IGRPEN0_read ()))))
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
                                                  else (R_set t (__get_ICC_IGRPEN0 (← (ICC_IGRPEN0_read ())))))))))))))))
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
                              else (R_set t (__get_ICC_IGRPEN0 (← (ICC_IGRPEN0_read ())))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (R_set t (__get_ICC_IGRPEN0 (← (ICC_IGRPEN0_read ())))))
              else (pure ()))))


