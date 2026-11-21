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
def BRBSRC_EL1_SysRegRead_3ce62e599c7c836c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 19))))))))
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
                          else
                            (do
                              if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 19)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 19)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_42de11a512022e40 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 18))))))))
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
                          else
                            (do
                              if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 18)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 18)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_442e3527ac440384 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((16 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 16))))))))
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
                          else
                            (do
                              if (((16 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 16)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((16 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 16)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_4a79da6f3039aa0b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((5 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 5))))))))
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
                          else
                            (do
                              if (((5 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 5)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((5 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 5)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_52d32e2fdd778cdd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((13 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 13))))))))
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
                          else
                            (do
                              if (((13 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 13)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((13 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 13)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_54e43d4416534fcb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((3 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 3))))))))
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
                          else
                            (do
                              if (((3 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 3)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((3 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_561515c0c6afe1b8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((26 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 26))))))))
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
                          else
                            (do
                              if (((26 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 26)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((26 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 26)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_5b4b28442256ea43 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((15 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 15))))))))
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
                          else
                            (do
                              if (((15 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 15)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((15 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 15)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_5dedf70f29c9772d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 2))))))))
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
                          else
                            (do
                              if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 2)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_612f81995305025e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((1 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 1))))))))
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
                          else
                            (do
                              if (((1 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((1 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_629d83cb2c3319a3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((30 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 30))))))))
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
                          else
                            (do
                              if (((30 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 30)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((30 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 30)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_66c1c459776c066e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((27 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 27))))))))
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
                          else
                            (do
                              if (((27 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 27)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((27 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 27)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_6a646a8b097b9662 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((17 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 17))))))))
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
                          else
                            (do
                              if (((17 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 17)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((17 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 17)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_6c5c1f71c6436b80 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((10 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 10))))))))
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
                          else
                            (do
                              if (((10 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 10)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((10 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 10)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_7c36b32dfd995b27 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((6 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 6))))))))
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
                          else
                            (do
                              if (((6 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 6)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((6 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 6)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_832b319ba0979511 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((25 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 25))))))))
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
                          else
                            (do
                              if (((25 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 25)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((25 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 25)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_843d617412783cba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((12 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 12))))))))
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
                          else
                            (do
                              if (((12 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 12)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((12 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 12)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_867cb054c07cff2f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((9 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 9))))))))
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
                          else
                            (do
                              if (((9 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 9)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((9 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 9)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_97cc6af3e6810121 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((11 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 11))))))))
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
                          else
                            (do
                              if (((11 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 11)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((11 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 11)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_995cc54bcb3d899c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 0))))))))
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
                          else
                            (do
                              if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 0)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_a985e159abb6644f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((4 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 4))))))))
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
                          else
                            (do
                              if (((4 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 4)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((4 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 4)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_b1d7d5499745f113 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((24 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 24))))))))
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
                          else
                            (do
                              if (((24 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 24)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((24 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 24)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_cf9b7af02d181adc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((14 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 14))))))))
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
                          else
                            (do
                              if (((14 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 14)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((14 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 14)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_d2ff5f8a61d06f9b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((29 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 29))))))))
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
                          else
                            (do
                              if (((29 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 29)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((29 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 29)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_e1966593749d3d3f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((8 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 8))))))))
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
                          else
                            (do
                              if (((8 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 8)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((8 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 8)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_ef5027149f4fd69e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 28))))))))
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
                          else
                            (do
                              if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 28)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBSRC_EL1) 28)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGTINJ_EL1_SysRegRead_0e58e4379b298df5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else (X_set t 64 (← readReg BRBTGTINJ_EL1)))))))
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
                          else (X_set t 64 (← readReg BRBTGTINJ_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg BRBTGTINJ_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_0763623dddebed93 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((23 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 23))))))))
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
                          else
                            (do
                              if (((23 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 23)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((23 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 23)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_0b4f89fe1c4542ef (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((6 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 6))))))))
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
                          else
                            (do
                              if (((6 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 6)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((6 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 6)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_1af5178ad600d3a5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((11 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 11))))))))
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
                          else
                            (do
                              if (((11 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 11)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((11 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 11)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_1f756e7f398b2913 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((30 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 30))))))))
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
                          else
                            (do
                              if (((30 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 30)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((30 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 30)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_2323d292faaf2c52 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((7 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 7))))))))
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
                          else
                            (do
                              if (((7 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 7)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((7 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 7)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_2def60c5cd956968 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((1 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 1))))))))
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
                          else
                            (do
                              if (((1 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 1)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((1 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_39b283daffc26b48 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((24 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 24))))))))
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
                          else
                            (do
                              if (((24 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 24)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((24 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 24)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_3acb3c110dfc9028 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((17 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 17))))))))
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
                          else
                            (do
                              if (((17 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 17)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((17 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 17)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_45c85163047bb4e9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((4 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 4))))))))
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
                          else
                            (do
                              if (((4 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 4)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((4 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 4)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_4a26f7681cbb4b61 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((27 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 27))))))))
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
                          else
                            (do
                              if (((27 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 27)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((27 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 27)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_523b8e4201ff85d3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 19))))))))
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
                          else
                            (do
                              if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 19)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 19)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_61af63a696814dc5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 0))))))))
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
                          else
                            (do
                              if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 0)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_6d006e7c7c1ea2f2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((12 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 12))))))))
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
                          else
                            (do
                              if (((12 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 12)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((12 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 12)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_71b2c8fc1498b4b2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((10 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 10))))))))
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
                          else
                            (do
                              if (((10 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 10)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((10 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 10)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_78b71d697e3a7c27 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((20 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 20))))))))
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
                          else
                            (do
                              if (((20 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 20)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((20 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 20)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_836220a18820905f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((13 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 13))))))))
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
                          else
                            (do
                              if (((13 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 13)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((13 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 13)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_901e3d710db08495 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((15 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 15))))))))
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
                          else
                            (do
                              if (((15 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 15)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((15 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 15)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_a1836a366d3770a4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((25 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 25))))))))
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
                          else
                            (do
                              if (((25 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 25)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((25 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 25)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_a19b60211eaf5d17 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((14 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 14))))))))
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
                          else
                            (do
                              if (((14 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 14)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((14 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 14)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_a58bd53c7eda75fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((5 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 5))))))))
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
                          else
                            (do
                              if (((5 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 5)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((5 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 5)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_ae456def5b2d3877 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((29 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 29))))))))
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
                          else
                            (do
                              if (((29 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 29)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((29 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 29)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_af7e58d50faba266 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((26 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 26))))))))
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
                          else
                            (do
                              if (((26 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 26)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((26 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 26)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_b9c401f4aafa6cae (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((8 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 8))))))))
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
                          else
                            (do
                              if (((8 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 8)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((8 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 8)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_c2018b407cd053ad (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((3 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 3))))))))
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
                          else
                            (do
                              if (((3 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 3)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((3 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_cea01bf612be4740 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 2))))))))
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
                          else
                            (do
                              if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 2)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_d0b2b38c41380e27 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((21 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 21))))))))
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
                          else
                            (do
                              if (((21 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 21)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((21 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 21)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_d83abc0d01ceb716 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((16 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 16))))))))
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
                          else
                            (do
                              if (((16 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 16)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((16 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 16)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_e6294ef271ec9fdd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((22 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 22))))))))
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
                          else
                            (do
                              if (((22 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 22)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((22 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 22)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_e84fec146c0ec53c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 31))))))))
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
                          else
                            (do
                              if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 31)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 31)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_f2e343a383a585f8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((9 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 9))))))))
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
                          else
                            (do
                              if (((9 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 9)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((9 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 9)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_f716b6b4ae3bca3e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 28))))))))
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
                          else
                            (do
                              if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 28)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 28)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTGT_EL1_SysRegRead_f85da45410915871 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else
                            (do
                              if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 18))))))))
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
                          else
                            (do
                              if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                              then (X_set t 64 (Zeros (n := 64)))
                              else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 18)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1))) *i 32)) ≥b 64) : Bool)
                  then (X_set t 64 (Zeros (n := 64)))
                  else (X_set t 64 (GetElem?.getElem! (← readReg BRBTGT_EL1) 18)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def BRBTS_EL1_SysRegRead_a92810602a111e63 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_SBRBE ← (( do (pure (_get_MDCR_EL3_Type_SBRBE (← readReg MDCR_EL3))) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_nBRBDATA ← (( do (pure (_get_HDFGRTR_EL2_Type_nBRBDATA (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_nBRBDATA == 0#1)) : Bool)
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
                          else (X_set t 64 (← readReg BRBTS_EL1)))))))
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
                          else (X_set t 64 (← readReg BRBTS_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg BRBTS_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CCSIDR2_EL1_SysRegRead_7161997c851583ee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID4 ← (( do (pure (_get_HCR_EL2_Type_TID4 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID2 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TID4 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_CCSIDR2_EL1 (← readReg CCSIDR2_EL1)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_CCSIDR2_EL1 (← readReg CCSIDR2_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CCSIDR2_EL1 (← readReg CCSIDR2_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CCSIDR_EL1_SysRegRead_5f1582fb2f446af0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID4 ← (( do (pure (_get_HCR_EL2_Type_TID4 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_CCSIDR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_CCSIDR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID2 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TID4 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_CCSIDR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_CCSIDR_EL1 (← readReg CCSIDR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_CCSIDR_EL1 (← readReg CCSIDR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CCSIDR_EL1 (← readReg CCSIDR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CLIDR_EL1_SysRegRead_e5c2643fd321419d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID4 ← (( do (pure (_get_HCR_EL2_Type_TID4 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_CLIDR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_CLIDR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_IDST)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (sailThrow ((Error_Undefined ())) : SailM Unit))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID2 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TID4 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_CLIDR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_CLIDR_EL1 (← readReg CLIDR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_CLIDR_EL1 (← readReg CLIDR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CLIDR_EL1 (← readReg CLIDR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTFRQ_EL0_SysRegRead_aed619ec0d882dc5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if ((←((pure (! (←((EL2Enabled ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))) <&&> (do
           (pure (((_get_CNTKCTL_EL1_Type_EL0PCTEN (← readReg CNTKCTL_EL1)) +++ (_get_CNTKCTL_EL1_Type_EL0VCTEN (← readReg CNTKCTL_EL1))) == 0b00#2))))) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
               (pure (((_get_CNTHCTL_EL2_Type_EL0PCTEN (← readReg CNTHCTL_EL2)) +++ (_get_CNTHCTL_EL2_Type_EL0VCTEN (← readReg CNTHCTL_EL2))) == 0b00#2))))) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (X_set t 64 (__get_CNTFRQ_EL0 (← readReg CNTFRQ_EL0)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (__get_CNTFRQ_EL0 (← readReg CNTFRQ_EL0)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_CNTFRQ_EL0 (← readReg CNTFRQ_EL0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CNTFRQ_EL0 (← readReg CNTFRQ_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHCTL_EL2_SysRegRead_25bfe781a33503e5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_CNTHCTL_EL2 (← readReg CNTHCTL_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CNTHCTL_EL2 (← readReg CNTHCTL_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHCTL_EL2_SysRegRead_c39dc9ffb55dc488 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (__get_CNTKCTL_EL1 (← readReg CNTKCTL_EL1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (__get_CNTHCTL_EL2 (← readReg CNTHCTL_EL2)))
              else (X_set t 64 (__get_CNTKCTL_EL1 (← readReg CNTKCTL_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CNTKCTL_EL1 (← readReg CNTKCTL_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHPS_CTL_EL2_SysRegRead_79f3fb88a16d36e6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PCEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0PTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PTEN == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                           (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                      then (X_set t 64 (__get_CNTHPS_CTL_EL2 (← readReg CNTHPS_CTL_EL2)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then (X_set t 64 (__get_CNTHP_CTL_EL2 (← readReg CNTHP_CTL_EL2)))
                          else (X_set t 64 (__get_CNTP_CTL_EL0 (← readReg CNTP_CTL_EL0)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x180#12))))
                  else (X_set t 64 (__get_CNTP_CTL_EL0 (← readReg CNTP_CTL_EL0))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then (X_set t 64 (__get_CNTHPS_CTL_EL2 (← readReg CNTHPS_CTL_EL2)))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then (X_set t 64 (__get_CNTHP_CTL_EL2 (← readReg CNTHP_CTL_EL2)))
                  else (X_set t 64 (__get_CNTP_CTL_EL0 (← readReg CNTP_CTL_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CNTP_CTL_EL0 (← readReg CNTP_CTL_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHPS_CTL_EL2_SysRegRead_9ed12a041f4d5569 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (X_set t 64 (__get_CNTHPS_CTL_EL2 (← readReg CNTHPS_CTL_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (__get_CNTHPS_CTL_EL2 (← readReg CNTHPS_CTL_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHPS_CVAL_EL2_SysRegRead_d2662865ff7936c3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (X_set t 64 (← readReg CNTHPS_CVAL_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (← readReg CNTHPS_CVAL_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHPS_TVAL_EL2_SysRegRead_893c5b3a9908faeb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHPS_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHPS_CTL_EL2_Type_ENABLE (← readReg CNTHPS_CTL_EL2))) ) : SailM (BitVec 1) )
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
                  if ((__CNTHPS_CTL_EL2_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTHPS_TVAL_EL2 (Mk_CNTHPS_TVAL_EL2_Type ((← readReg CNTHPS_CVAL_EL2) - (← (PhysicalCountInt ()))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__CNTHPS_CTL_EL2_ENABLE == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_CNTHPS_TVAL_EL2 (Mk_CNTHPS_TVAL_EL2_Type ((← readReg CNTHPS_CVAL_EL2) - (← (PhysicalCountInt ()))))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_CTL_EL2_SysRegRead_fc0ab47b2d1292cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_CNTHP_CTL_EL2 (← readReg CNTHP_CTL_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CNTHP_CTL_EL2 (← readReg CNTHP_CTL_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_CVAL_EL2_SysRegRead_5a841847b0720163 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← readReg CNTHP_CVAL_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg CNTHP_CVAL_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_CVAL_EL2_SysRegRead_ed1c928371f03392 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PCEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0PTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PTEN == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                           (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                      then (X_set t 64 (← readReg CNTHPS_CVAL_EL2))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then (X_set t 64 (← readReg CNTHP_CVAL_EL2))
                          else (X_set t 64 (← readReg CNTP_CVAL_EL0))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x178#12))))
                  else (X_set t 64 (← readReg CNTP_CVAL_EL0)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then (X_set t 64 (← readReg CNTHPS_CVAL_EL2))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then (X_set t 64 (← readReg CNTHP_CVAL_EL2))
                  else (X_set t 64 (← readReg CNTP_CVAL_EL0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg CNTP_CVAL_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_EL2_SysRegRead_ddcf2e9dd3ff2611 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHP_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHP_CTL_EL2_Type_ENABLE (← readReg CNTHP_CTL_EL2))) ) : SailM (BitVec 1) )
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
              if ((__CNTHP_CTL_EL2_ENABLE == 0#1) : Bool)
              then (X_set t 64 (← (__UNKNOWN_bits 64)))
              else (X_set t 64 (__get_CNTHP_TVAL_EL2 (Mk_CNTHP_TVAL_EL2_Type ((← readReg CNTHP_CVAL_EL2) - (← (PhysicalCountInt ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTHP_CTL_EL2_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTHP_TVAL_EL2 (Mk_CNTHP_TVAL_EL2_Type ((← readReg CNTHP_CVAL_EL2) - (← (PhysicalCountInt ())))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHVS_CTL_EL2_SysRegRead_1d2ef372c8b0dab1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0VTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VTEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                       (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                  then (X_set t 64 (__get_CNTHVS_CTL_EL2 (← readReg CNTHVS_CTL_EL2)))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                      then (X_set t 64 (__get_CNTHV_CTL_EL2 (← readReg CNTHV_CTL_EL2)))
                      else (X_set t 64 (__get_CNTV_CTL_EL0 (← readReg CNTV_CTL_EL0))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x170#12))))
              else (X_set t 64 (__get_CNTV_CTL_EL0 (← readReg CNTV_CTL_EL0)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then (X_set t 64 (__get_CNTHVS_CTL_EL2 (← readReg CNTHVS_CTL_EL2)))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then (X_set t 64 (__get_CNTHV_CTL_EL2 (← readReg CNTHV_CTL_EL2)))
                  else (X_set t 64 (__get_CNTV_CTL_EL0 (← readReg CNTV_CTL_EL0)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CNTV_CTL_EL0 (← readReg CNTV_CTL_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHVS_CTL_EL2_SysRegRead_46708ffedf6618c4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (X_set t 64 (__get_CNTHVS_CTL_EL2 (← readReg CNTHVS_CTL_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (__get_CNTHVS_CTL_EL2 (← readReg CNTHVS_CTL_EL2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHVS_CVAL_EL2_SysRegRead_e87d470dc26af07a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              else (X_set t 64 (← readReg CNTHVS_CVAL_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (X_set t 64 (← readReg CNTHVS_CVAL_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHVS_TVAL_EL2_SysRegRead_7b30facaa926411e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHVS_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHVS_CTL_EL2_Type_ENABLE (← readReg CNTHVS_CTL_EL2))) ) : SailM (BitVec 1) )
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
                  if ((__CNTHVS_CTL_EL2_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTHVS_TVAL_EL2 (Mk_CNTHVS_TVAL_EL2_Type ((← readReg CNTHVS_CVAL_EL2) - (← (PhysicalCountInt ()))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if ((__CNTHVS_CTL_EL2_ENABLE == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_CNTHVS_TVAL_EL2 (Mk_CNTHVS_TVAL_EL2_Type ((← readReg CNTHVS_CVAL_EL2) - (← (PhysicalCountInt ()))))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHV_CTL_EL2_SysRegRead_fe7c25cca2e88b3f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_CNTHV_CTL_EL2 (← readReg CNTHV_CTL_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CNTHV_CTL_EL2 (← readReg CNTHV_CTL_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHV_CVAL_EL2_SysRegRead_7bb539c281c21387 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← readReg CNTHV_CVAL_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg CNTHV_CVAL_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHV_CVAL_EL2_SysRegRead_aa1abdb084701418 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0VTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VTEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                       (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                  then (X_set t 64 (← readReg CNTHVS_CVAL_EL2))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                      then (X_set t 64 (← readReg CNTHV_CVAL_EL2))
                      else (X_set t 64 (← readReg CNTV_CVAL_EL0)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
              then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x168#12))))
              else (X_set t 64 (← readReg CNTV_CVAL_EL0))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then (X_set t 64 (← readReg CNTHVS_CVAL_EL2))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then (X_set t 64 (← readReg CNTHV_CVAL_EL2))
                  else (X_set t 64 (← readReg CNTV_CVAL_EL0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg CNTV_CVAL_EL0))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHV_TVAL_EL2_SysRegRead_131a29f8b5d31ce1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHVS_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHVS_CTL_EL2_Type_ENABLE (← readReg CNTHVS_CTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHV_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHV_CTL_EL2_Type_ENABLE (← readReg CNTHV_CTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTV_CTL_EL0_ENABLE ← (( do (pure (_get_CNTV_CTL_EL0_Type_ENABLE (← readReg CNTV_CTL_EL0))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0VTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VTEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                       (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                  then
                    (do
                      if ((__CNTHVS_CTL_EL2_ENABLE == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTHVS_CVAL_EL2) - (← (PhysicalCountInt ())))))))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                      then
                        (do
                          if ((__CNTHV_CTL_EL2_ENABLE == 0#1) : Bool)
                          then (X_set t 64 (← (__UNKNOWN_bits 64)))
                          else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTHV_CVAL_EL2) - (← (PhysicalCountInt ())))))))
                      else
                        (do
                          if ((←((pure (HaveEL EL2)) <&&> (do
                               (pure (! (← (EL2Enabled ())))) <||> (do
                                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2)))))) : Bool)
                          then
                            (do
                              if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                              then (X_set t 64 (← (__UNKNOWN_bits 64)))
                              else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTV_CVAL_EL0) - ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)))))))
                          else
                            (do
                              if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                              then (X_set t 64 (← (__UNKNOWN_bits 64)))
                              else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTV_CVAL_EL0) - (← (PhysicalCountInt ())))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__CNTHCTL_EL2_EL1TVT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((HaveEL EL2) : Bool)
              then
                (do
                  if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTV_CVAL_EL0) - ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)))))))
              else
                (do
                  if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTV_CVAL_EL0) - (← (PhysicalCountInt ())))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then
                (do
                  if ((__CNTHVS_CTL_EL2_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTHVS_CVAL_EL2) - (← (PhysicalCountInt ())))))))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then
                    (do
                      if ((__CNTHV_CTL_EL2_ENABLE == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTHV_CVAL_EL2) - (← (PhysicalCountInt ())))))))
                  else
                    (do
                      if (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1) : Bool)
                      then
                        (do
                          if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                          then (X_set t 64 (← (__UNKNOWN_bits 64)))
                          else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTV_CVAL_EL0) - ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)))))))
                      else
                        (do
                          if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                          then (X_set t 64 (← (__UNKNOWN_bits 64)))
                          else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTV_CVAL_EL0) - (← (PhysicalCountInt ()))))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else
                    (do
                      if ((←((pure (HaveEL EL2)) <&&> (do
                           (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
                      then (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTV_CVAL_EL0) - ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2))))))
                      else
                        (do
                          if ((←((pure (HaveEL EL2)) <&&> (do
                               (ELUsingAArch32 EL2)))) : Bool)
                          then (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTV_CVAL_EL0) - ((← (PhysicalCountInt ())) - (← (CNTVOFF_read ())))))))
                          else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTV_CVAL_EL0) - (← (PhysicalCountInt ())))))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTHV_TVAL_EL2_SysRegRead_42829873ebd7042d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHV_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHV_CTL_EL2_Type_ENABLE (← readReg CNTHV_CTL_EL2))) ) : SailM (BitVec 1) )
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
              if ((__CNTHV_CTL_EL2_ENABLE == 0#1) : Bool)
              then (X_set t 64 (← (__UNKNOWN_bits 64)))
              else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTHV_CVAL_EL2) - (← (PhysicalCountInt ())))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTHV_CTL_EL2_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type ((← readReg CNTHV_CVAL_EL2) - (← (PhysicalCountInt ())))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTKCTL_EL1_SysRegRead_dfa3587117fd7e6d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (__get_CNTKCTL_EL1 (← readReg CNTKCTL_EL1)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_CNTKCTL_EL1 (← readReg CNTKCTL_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTPCT_EL0_SysRegRead_30a0e264d583fe56 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PCTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PCTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCTEN ← (( do
    (pure (BitVec.slice (← readReg CNTHCTL_EL2)
        (← (do
          if ((←((IsFeatureImplemented FEAT_VHE) <&&> (do
               (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))) : Bool)
          then (pure 10)
          else (pure 0))) 1)) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PCTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PCTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ECVEn ← (( do (pure (_get_SCR_EL3_Type_ECVEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_ECV ← (( do (pure (_get_CNTHCTL_EL2_Type_ECV (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0PCTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if ((((← (EL2Enabled ())) && (__HCR_EL2_E2H == 0#1)) && (__CNTHCTL_EL2_EL1PCTEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PCTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PCTEN == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((pure (((←((IsFeatureImplemented FEAT_ECV) <&&> (do (EL2Enabled ())))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1))) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) : Bool)
                      then (X_set t 64 ((← (PhysicalCountInt ())) - (← readReg CNTPOFF_EL2)))
                      else (X_set t 64 (← (PhysicalCountInt ()))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__CNTHCTL_EL2_EL1PCTEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((IsFeatureImplemented FEAT_ECV) <&&> (do
                       (EL2Enabled ())))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1)) : Bool)
              then (X_set t 64 ((← (PhysicalCountInt ())) - (← readReg CNTPOFF_EL2)))
              else (X_set t 64 (← (PhysicalCountInt ())))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← (PhysicalCountInt ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← (PhysicalCountInt ())))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTPOFF_EL2_SysRegRead_bfece51207f46d78 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ECVEn ← (( do (pure (_get_SCR_EL3_Type_ECVEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x1A8#12))))
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__SCR_EL3_ECVEn == 0#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_ECVEn == 0#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (← readReg CNTPOFF_EL2))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg CNTPOFF_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTPS_CTL_EL1_SysRegRead_b28f26339dbc713f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ST ← (( do (pure (_get_SCR_EL3_Type_ST (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__SCR_EL3_NS == 0#1)) : Bool)
          then
            (do
              if ((__SCR_EL3_EEL2 == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__SCR_EL3_ST == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_CNTPS_CTL_EL1 (← readReg CNTPS_CTL_EL1)))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CNTPS_CTL_EL1 (← readReg CNTPS_CTL_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTPS_CVAL_EL1_SysRegRead_21e9c10a0f76a1d1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ST ← (( do (pure (_get_SCR_EL3_Type_ST (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__SCR_EL3_NS == 0#1)) : Bool)
          then
            (do
              if ((__SCR_EL3_EEL2 == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__SCR_EL3_ST == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (← readReg CNTPS_CVAL_EL1))))
          else (sailThrow ((Error_Undefined ())) : SailM Unit))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg CNTPS_CVAL_EL1))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTPS_TVAL_EL1_SysRegRead_748a1753bd033377 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCR_EL3_NS ← (( do (pure (_get_SCR_EL3_Type_NS (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_EEL2 ← (( do (pure (_get_SCR_EL3_Type_EEL2 (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ST ← (( do (pure (_get_SCR_EL3_Type_ST (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ECVEn ← (( do (pure (_get_SCR_EL3_Type_ECVEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_ECV ← (( do (pure (_get_CNTHCTL_EL2_Type_ECV (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTPS_CTL_EL1_ENABLE ← (( do (pure (_get_CNTPS_CTL_EL1_Type_ENABLE (← readReg CNTPS_CTL_EL1))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__SCR_EL3_NS == 0#1)) : Bool)
          then
            (do
              if ((__SCR_EL3_EEL2 == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((__SCR_EL3_ST == 0#1) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((((←((IsFeatureImplemented FEAT_ECV) <&&> (do
                               (EL2Enabled ())))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1)) : Bool)
                      then
                        (do
                          if ((__CNTPS_CTL_EL1_ENABLE == 0#1) : Bool)
                          then (X_set t 64 (← (__UNKNOWN_bits 64)))
                          else (X_set t 64 (__get_CNTPS_TVAL_EL1 (Mk_CNTPS_TVAL_EL1_Type ((← readReg CNTPS_CVAL_EL1) - ((← (PhysicalCountInt ())) - (← readReg CNTPOFF_EL2)))))))
                      else
                        (do
                          if ((__CNTPS_CTL_EL1_ENABLE == 0#1) : Bool)
                          then (X_set t 64 (← (__UNKNOWN_bits 64)))
                          else (X_set t 64 (__get_CNTPS_TVAL_EL1 (Mk_CNTPS_TVAL_EL1_Type ((← readReg CNTPS_CVAL_EL1) - (← (PhysicalCountInt ()))))))))))
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
                  if ((__CNTPS_CTL_EL1_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTPS_TVAL_EL1 (Mk_CNTPS_TVAL_EL1_Type ((← readReg CNTPS_CVAL_EL1) - (← (PhysicalCountInt ())))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTP_CTL_EL0_SysRegRead_15357e2547a6f65f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTHCTL_EL2_EL1NVPCT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1NVPCT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
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
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1NVPCT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (← (NVMem_read (BitVec.toNat 0x180#12)))))
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
              then (X_set t 64 (__get_CNTP_CTL_EL0 (← readReg CNTP_CTL_EL0)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_CNTP_CTL_EL0 (← readReg CNTP_CTL_EL0)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTP_CVAL_EL0_SysRegRead_ea3c2820c47244b3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTHCTL_EL2_EL1NVPCT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1NVPCT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
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
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1NVPCT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (← (NVMem_read (BitVec.toNat 0x178#12)))))
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
              then (X_set t 64 (← readReg CNTP_CVAL_EL0))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg CNTP_CVAL_EL0))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTP_TVAL_EL0_SysRegRead_65dd187dcad1babf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTP_CTL_EL0_ENABLE ← (( do (pure (_get_CNTP_CTL_EL0_Type_ENABLE (← readReg CNTP_CTL_EL0))) ) : SailM (BitVec 1) )
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
              then
                (do
                  if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTP_CVAL_EL0) - (← (PhysicalCountInt ())))))))
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
                      if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTP_CVAL_EL0) - (← (PhysicalCountInt ())))))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTP_TVAL_EL0_SysRegRead_aa86b862886b57ac (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0PTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0PTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PCEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PCEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0PTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0PTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHPS_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHPS_CTL_EL2_Type_ENABLE (← readReg CNTHPS_CTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHP_CTL_EL2_ENABLE ← (( do (pure (_get_CNTHP_CTL_EL2_Type_ENABLE (← readReg CNTHP_CTL_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_ECVEn ← (( do (pure (_get_SCR_EL3_Type_ECVEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_ECV ← (( do (pure (_get_CNTHCTL_EL2_Type_ECV (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTP_CTL_EL0_ENABLE ← (( do (pure (_get_CNTP_CTL_EL0_Type_ENABLE (← readReg CNTP_CTL_EL0))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0PTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b10#2))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0PTEN == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                           (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                           (IsFeatureImplemented FEAT_SEL2)))) : Bool)
                      then
                        (do
                          if ((__CNTHPS_CTL_EL2_ENABLE == 0#1) : Bool)
                          then (X_set t 64 (← (__UNKNOWN_bits 64)))
                          else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTHPS_CVAL_EL2) - (← (PhysicalCountInt ())))))))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))) <&&> (do
                               (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                          then
                            (do
                              if ((__CNTHP_CTL_EL2_ENABLE == 0#1) : Bool)
                              then (X_set t 64 (← (__UNKNOWN_bits 64)))
                              else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTHP_CVAL_EL2) - (← (PhysicalCountInt ())))))))
                          else
                            (do
                              if ((←((pure (((←((IsFeatureImplemented FEAT_ECV) <&&> (do (EL2Enabled ())))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1))) <&&> (do
                                   (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) : Bool)
                              then
                                (do
                                  if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                                  else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTP_CVAL_EL0) - ((← (PhysicalCountInt ())) - (← readReg CNTPOFF_EL2)))))))
                              else
                                (do
                                  if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                                  else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTP_CVAL_EL0) - (← (PhysicalCountInt ()))))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))) && (__CNTHCTL_EL2_EL1PCEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))) && (__CNTHCTL_EL2_EL1PTEN == 0#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((IsFeatureImplemented FEAT_ECV) <&&> (do
                           (EL2Enabled ())))) && (__SCR_EL3_ECVEn == 1#1)) && (__CNTHCTL_EL2_ECV == 1#1)) : Bool)
                  then
                    (do
                      if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTP_CVAL_EL0) - ((← (PhysicalCountInt ())) - (← readReg CNTPOFF_EL2)))))))
                  else
                    (do
                      if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTP_CVAL_EL0) - (← (PhysicalCountInt ()))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))) <&&> (do
                   (IsFeatureImplemented FEAT_SEL2)))) : Bool)
              then
                (do
                  if ((__CNTHPS_CTL_EL2_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTHPS_CVAL_EL2) - (← (PhysicalCountInt ())))))))
              else
                (do
                  if ((←((pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 1#1))))) : Bool)
                  then
                    (do
                      if ((__CNTHP_CTL_EL2_ENABLE == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTHP_CVAL_EL2) - (← (PhysicalCountInt ())))))))
                  else
                    (do
                      if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTP_CVAL_EL0) - (← (PhysicalCountInt ())))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type ((← readReg CNTP_CVAL_EL0) - (← (PhysicalCountInt ())))))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTVCT_EL0_SysRegRead_1d562372e622baf9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTKCTL_EL1_EL0VCTEN ← (( do (pure (_get_CNTKCTL_EL1_Type_EL0VCTEN (← readReg CNTKCTL_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL0VCTEN ← (( do (pure (_get_CNTHCTL_EL2_Type_EL0VCTEN (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __CNTHCTL_EL2_EL1TVCT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1TVCT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__CNTKCTL_EL1_EL0VCTEN == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__CNTHCTL_EL2_EL0VCTEN == 0#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1TVCT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((pure (HaveEL EL2)) <&&> (do
                       (pure (! (← (EL2Enabled ())))) <||> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2)))))) : Bool)
                  then (X_set t 64 ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)))
                  else (X_set t 64 (← (PhysicalCountInt ())))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__CNTHCTL_EL2_EL1TVCT == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((HaveEL EL2) : Bool)
              then (X_set t 64 ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)))
              else (X_set t 64 (← (PhysicalCountInt ())))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 0#1) : Bool)
              then (X_set t 64 ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)))
              else (X_set t 64 (← (PhysicalCountInt ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((←((pure (HaveEL EL2)) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
                  then (X_set t 64 ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)))
                  else
                    (do
                      if ((←((pure (HaveEL EL2)) <&&> (do
                           (ELUsingAArch32 EL2)))) : Bool)
                      then (X_set t 64 ((← (PhysicalCountInt ())) - (← (CNTVOFF_read ()))))
                      else (X_set t 64 (← (PhysicalCountInt ())))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTVOFF_EL2_SysRegRead_f84a995c7f5f427c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x060#12))))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (sailThrow ((Error_Undefined ())) : SailM Unit)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (← readReg CNTVOFF_EL2))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (← readReg CNTVOFF_EL2))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTV_CTL_EL0_SysRegRead_23c5b36dc5cb110e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTHCTL_EL2_EL1NVVCT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1NVVCT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
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
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1NVVCT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (← (NVMem_read (BitVec.toNat 0x170#12)))))
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
              then (X_set t 64 (__get_CNTV_CTL_EL0 (← readReg CNTV_CTL_EL0)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_CNTV_CTL_EL0 (← readReg CNTV_CTL_EL0)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTV_CVAL_EL0_SysRegRead_e31d635daf585919 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __CNTHCTL_EL2_EL1NVVCT ← (( do (pure (_get_CNTHCTL_EL2_Type_EL1NVVCT (← readReg CNTHCTL_EL2))) ) : SailM (BitVec 1) )
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
          then
            (do
              if (((←((EL2Enabled ()) <&&> (do
                     (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__CNTHCTL_EL2_EL1NVVCT == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (← (NVMem_read (BitVec.toNat 0x168#12)))))
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
              then (X_set t 64 (← readReg CNTV_CVAL_EL0))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (← readReg CNTV_CVAL_EL0))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CNTV_TVAL_EL0_SysRegRead_f682815b8c52312a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __CNTV_CTL_EL0_ENABLE ← (( do (pure (_get_CNTV_CTL_EL0_Type_ENABLE (← readReg CNTV_CTL_EL0))) ) : SailM (BitVec 1) )
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
              then
                (do
                  if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                  then (X_set t 64 (← (__UNKNOWN_bits 64)))
                  else (X_set t 64 (__get_CNTV_TVAL_EL0 (Mk_CNTV_TVAL_EL0_Type ((← readReg CNTV_CVAL_EL0) - ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)))))))
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
                      if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                      then (X_set t 64 (← (__UNKNOWN_bits 64)))
                      else (X_set t 64 (__get_CNTV_TVAL_EL0 (Mk_CNTV_TVAL_EL0_Type ((← readReg CNTV_CVAL_EL0) - ((← (PhysicalCountInt ())) - (← readReg CNTVOFF_EL2)))))))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CONTEXTIDR_EL1_SysRegRead_c6da578db1984530 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x108#12))))
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
              then (X_set t 64 (__get_CONTEXTIDR_EL1 (← readReg CONTEXTIDR_EL1)))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_CONTEXTIDR_EL1 (← readReg CONTEXTIDR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CONTEXTIDR_EL2_SysRegRead_0a5ce1fa99f54107 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TRVM ← (( do (pure (_get_HCR_EL2_Type_TRVM (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_CONTEXTIDR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_CONTEXTIDR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TRVM == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_CONTEXTIDR_EL1 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                  then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x108#12))))
                  else (X_set t 64 (__get_CONTEXTIDR_EL1 (← readReg CONTEXTIDR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then (X_set t 64 (__get_CONTEXTIDR_EL2 (← readReg CONTEXTIDR_EL2)))
              else (X_set t 64 (__get_CONTEXTIDR_EL1 (← readReg CONTEXTIDR_EL1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CONTEXTIDR_EL1 (← readReg CONTEXTIDR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CONTEXTIDR_EL2_SysRegRead_dc0e6b987e373678 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then (X_set t 64 (__get_CONTEXTIDR_EL2 (← readReg CONTEXTIDR_EL2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CONTEXTIDR_EL2 (← readReg CONTEXTIDR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPACR_EL1_SysRegRead_00e702278c481e13 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TCPAC ← (( do (pure (_get_CPTR_EL3_Type_TCPAC (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b101#3))))) : Bool)
          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x100#12))))
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
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else (X_set t 64 (__get_CPACR_EL1 (← readReg CPACR_EL1)))))
              else (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL2))))))) && (__HCR_EL2_E2H == 1#1)) : Bool)
                  then (X_set t 64 (__get_CPACR_EL1 (← readReg CPACR_EL1)))
                  else (sailThrow ((Error_Undefined ())) : SailM Unit))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPACR_EL1_SysRegRead_3ecedf6fe7690be4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TCPAC ← (( do (pure (_get_CPTR_EL3_Type_TCPAC (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
  let __CPTR_EL2_TCPAC ← (( do (pure (_get_CPTR_EL2_Type_TCPAC (← readReg CPTR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_CPACR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_CPACR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_E2H ← (( do (pure (_get_HCR_EL2_Type_E2H (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                 (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if (((← (EL2Enabled ())) && (__CPTR_EL2_TCPAC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_CPACR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                      then
                        (do
                          if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if ((←((EL2Enabled ()) <&&> (do
                               (pure (((_get_HCR_EL2_Type_NV2 (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV (← readReg HCR_EL2)))) == 0b111#3))))) : Bool)
                          then (X_set t 64 (← (NVMem_read (BitVec.toNat 0x100#12))))
                          else (X_set t 64 (__get_CPACR_EL1 (← readReg CPACR_EL1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then (X_set t 64 (__get_CPTR_EL2 (← readReg CPTR_EL2)))
                      else (X_set t 64 (__get_CPACR_EL1 (← readReg CPACR_EL1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CPACR_EL1 (← readReg CPACR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPTR_EL2_SysRegRead_70f3036b7ed095c4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __CPTR_EL3_TCPAC ← (( do (pure (_get_CPTR_EL3_Type_TCPAC (← readReg CPTR_EL3))) ) : SailM (BitVec 1) )
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
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                  then
                    (do
                      if (((← (Halted ())) && (__EDSCR_SDD == 1#1)) : Bool)
                      then (sailThrow ((Error_Undefined ())) : SailM Unit)
                      else (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else (X_set t 64 (__get_CPTR_EL2 (← readReg CPTR_EL2)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CPTR_EL2 (← readReg CPTR_EL2)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CPTR_EL3_SysRegRead_7b3995450955fa38 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              then (X_set t 64 (__get_CPTR_EL3 (← readReg CPTR_EL3)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CSSELR_EL1_SysRegRead_5913225fc951e4d2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID4 ← (( do (pure (_get_HCR_EL2_Type_TID4 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_CSSELR_EL1 ← (( do (pure (_get_HFGRTR_EL2_Type_CSSELR_EL1 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID2 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if (((← (EL2Enabled ())) && (__HCR_EL2_TID4 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_CSSELR_EL1 == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_CSSELR_EL1 (← readReg CSSELR_EL1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_CSSELR_EL1 (← readReg CSSELR_EL1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CSSELR_EL1 (← readReg CSSELR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CTR_EL0_SysRegRead_17103694dd49566e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UCT ← (( do (pure (_get_SCTLR_EL1_Type_UCT (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TID2 ← (( do (pure (_get_HCR_EL2_Type_TID2 (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HFGRTR_EL2_CTR_EL0 ← (( do (pure (_get_HFGRTR_EL2_Type_CTR_EL0 (← readReg HFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __SCTLR_EL2_UCT ← (( do (pure (_get_SCTLR_EL2_Type_UCT (← readReg SCTLR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((! (←((EL2Enabled ()) <&&> (do
               (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2)))))) && (__SCTLR_EL1_UCT == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          if (((←((EL2Enabled ()) <&&> (do
                 (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))))) && (__HCR_EL2_TID2 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2))) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_CTR_EL0 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if (((←((EL2Enabled ()) <&&> (do
                         (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) && (__SCTLR_EL2_UCT == 0#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else (X_set t 64 (__get_CTR_EL0 (← readReg CTR_EL0)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TID2 == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else
            (do
              if ((((←((EL2Enabled ()) <&&> (do
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HFGRTR_EL2_CTR_EL0 == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (X_set t 64 (__get_CTR_EL0 (← readReg CTR_EL0)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (__get_CTR_EL0 (← readReg CTR_EL0)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_CTR_EL0 (← readReg CTR_EL0)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def CurrentEL_SysRegRead_94be544516d41cc8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if (((← readReg PSTATE).EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL1) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_NV == 1#1)) : Bool)
          then (X_set t 64 (((Zeros (n := 60)) +++ 0b10#2) +++ (Zeros (n := 2))))
          else (X_set t 64 (((Zeros (n := 60)) +++ (← readReg PSTATE).EL) +++ (Zeros (n := 2)))))
      else
        (do
          if (((← readReg PSTATE).EL == EL2) : Bool)
          then (X_set t 64 (((Zeros (n := 60)) +++ (← readReg PSTATE).EL) +++ (Zeros (n := 2))))
          else
            (do
              if (((← readReg PSTATE).EL == EL3) : Bool)
              then (X_set t 64 (((Zeros (n := 60)) +++ (← readReg PSTATE).EL) +++ (Zeros (n := 2))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DACR32_EL2_SysRegRead_7553854be98ecb11 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __HCR_EL2_NV ← (( do (pure (_get_HCR_EL2_Type_NV (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((! (HaveAArch32EL EL1)) : Bool)
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
              then (X_set t 64 (__get_DACR32_EL2 (← readReg DACR32_EL2)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_DACR32_EL2 (← readReg DACR32_EL2)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DAIF_SysRegRead_102c97f1f2780854 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __SCTLR_EL1_UMA ← (( do (pure (_get_SCTLR_EL1_Type_UMA (← readReg SCTLR_EL1))) ) : SailM (BitVec 1) )
  let __HCR_EL2_TGE ← (( do (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      if (((←((EL2Enabled ()) <&&> (do
             (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) || (__SCTLR_EL1_UMA == 0#1)) : Bool)
      then
        (do
          if (((← (EL2Enabled ())) && (__HCR_EL2_TGE == 1#1)) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (X_set t 64 (((Zeros (n := 54)) +++ ((← readReg PSTATE).D +++ ((← readReg PSTATE).A +++ ((← readReg PSTATE).I +++ (← readReg PSTATE).F)))) +++ (Zeros (n := 6)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then (X_set t 64 (((Zeros (n := 54)) +++ ((← readReg PSTATE).D +++ ((← readReg PSTATE).A +++ ((← readReg PSTATE).I +++ (← readReg PSTATE).F)))) +++ (Zeros (n := 6))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then (X_set t 64 (((Zeros (n := 54)) +++ ((← readReg PSTATE).D +++ ((← readReg PSTATE).A +++ ((← readReg PSTATE).I +++ (← readReg PSTATE).F)))) +++ (Zeros (n := 6))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (((Zeros (n := 54)) +++ ((← readReg PSTATE).D +++ ((← readReg PSTATE).A +++ ((← readReg PSTATE).I +++ (← readReg PSTATE).F)))) +++ (Zeros (n := 6))))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGAUTHSTATUS_EL1_SysRegRead_d85001e86a493d96 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGAUTHSTATUS_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGAUTHSTATUS_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGAUTHSTATUS_EL1 == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_DBGAUTHSTATUS_EL1 (← readReg DBGAUTHSTATUS_EL1)))))))
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
                  else (X_set t 64 (__get_DBGAUTHSTATUS_EL1 (← readReg DBGAUTHSTATUS_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_DBGAUTHSTATUS_EL1 (← readReg DBGAUTHSTATUS_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_0eb0d62ea2fda071 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (15 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 15)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 15)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 15)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_1e5042e13523fa5d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (13 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 13)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 13)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 13)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_25ce85c39c7f6fab (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (12 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 12)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 12)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 12)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_34c274725a4c52be (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (6 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 6)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 6)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 6)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_351735ec7986860c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (3 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 3)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 3)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 3)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_3fab4f560940f3bb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (0 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 0)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 0)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 0)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_4819f7c1472ce09b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (10 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 10)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 10)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 10)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_4aa6676517b46c9d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (11 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 11)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 11)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 11)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_8ee7203ab64efc9b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (9 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 9)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 9)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 9)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_8fd16782f7a14e94 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (4 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 4)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 4)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 4)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_92bc7c55fdf9f90f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (7 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 7)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 7)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 7)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_9b50139a1fa842ce (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (1 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 1)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 1)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 1)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_cdb3eeaee7600974 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (8 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 8)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 8)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 8)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_cf52c5b94cb6cfbc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (14 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 14)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 14)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 14)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_dfb30cff5c993bc8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (2 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 2)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 2)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 2)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegRead_ee9d701f728184a3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBCRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (5 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBCRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                                  else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 5)))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                              else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 5)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)))))
                          else (X_set t 64 (__get_DBGBCR_EL1 (GetElem?.getElem! (← readReg DBGBCR_EL1) 5)))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_08fe9aa719e4e44c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (1 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 1))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 1))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (1 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 1))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_25b8861425ee4c26 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (5 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 5))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 5))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (5 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 5))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_351ab37f466f6889 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (11 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 11))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 11))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (11 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 11))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_5ed77d081c253be3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (0 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 0))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 0))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (0 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 0))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_755afa7df870d9ab (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (7 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 7))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 7))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (7 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 7))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_7e4c0d4f3367d780 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (2 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 2))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 2))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (2 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 2))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_8a3cda8f4660427a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (12 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 12))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 12))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (12 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 12))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_8c3e53570d26ce7a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (10 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 10))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 10))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (10 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 10))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_9deb23233bdb8631 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (4 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 4))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 4))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (4 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 4))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_a18f410293f246c4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (8 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 8))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 8))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (8 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 8))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_a6904466fe9c7a54 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (3 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 3))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 3))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (3 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 3))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_ab88cca85ec0eca9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (9 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 9))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 9))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (9 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 9))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_c3ec1516735db5f7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (14 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 14))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 14))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (14 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 14))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_c5088163afaa4276 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (6 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 6))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 6))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (6 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 6))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_d4c2dcc933af38a7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (13 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 13))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 13))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (13 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 13))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGBVR_EL1_SysRegRead_d8b7590f7c00d19c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGBVRn_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((←((pure (! (← (IsFeatureImplemented FEAT_Debugv8p9)))) <&&> (do
       (pure (15 ≥b (← readReg NUM_BREAKPOINTS)))) <||> (do
       (IsFeatureImplemented FEAT_Debugv8p9) <&&> (do
         (pure ((15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16)) ≥b (← readReg NUM_BREAKPOINTS))))))) : Bool)
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
              if (((←((pure (((← (Halted ())) && (HaveEL EL3)) && (__EDSCR_SDD == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((((←((EL2Enabled ()) <&&> (do
                           (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGBVRn_EL1 == 1#1)) : Bool)
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
                              if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else
                                (do
                                  if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                                  then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                                  else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 15))))))))
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
                          if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else
                            (do
                              if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                              then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                              else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 15))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else
                        (do
                          if ((← (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
                          then (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) (15 +i ((BitVec.toNat (← (EffectiveMDSELR_EL1_BANK ()))) *i 16))))
                          else (X_set t 64 (GetElem?.getElem! (← readReg DBGBVR_EL1) 15))))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGCLAIMCLR_EL1_SysRegRead_ffbb497475eb383a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGCLAIM ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGCLAIM (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGCLAIM == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_DBGCLAIMCLR_EL1 (← readReg DBGCLAIMCLR_EL1)))))))
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
                  else (X_set t 64 (__get_DBGCLAIMCLR_EL1 (← readReg DBGCLAIMCLR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_DBGCLAIMCLR_EL1 (← readReg DBGCLAIMCLR_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGCLAIMSET_EL1_SysRegRead_e478959c32681458 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGCLAIM ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGCLAIM (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGCLAIM == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_DBGCLAIMSET_EL1 (← readReg DBGCLAIMSET_EL1)))))))
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
                  else (X_set t 64 (__get_DBGCLAIMSET_EL1 (← readReg DBGCLAIMSET_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_DBGCLAIMSET_EL1 (← readReg DBGCLAIMSET_EL1)))
              else (pure ()))))

/-- Type quantifiers: t : Int -/
def DBGDTRRX_EL0_SysRegRead_54d73d4619fa5dbf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  if ((← (Halted ())) : Bool)
  then (X_set t 64 (__get_DBGDTRRX_EL0 (← readReg DBGDTRRX_EL0)))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if ((__MDSCR_EL1_TDCC == 1#1) : Bool)
          then
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do
                         (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2)))))) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                          else (X_set t 64 (__get_DBGDTRRX_EL0 (← readReg DBGDTRRX_EL0))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
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
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                          else (X_set t 64 (__get_DBGDTRRX_EL0 (← readReg DBGDTRRX_EL0)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else (X_set t 64 (__get_DBGDTRRX_EL0 (← readReg DBGDTRRX_EL0)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (__get_DBGDTRRX_EL0 (← readReg DBGDTRRX_EL0)))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGDTR_EL0_SysRegRead_59f5860954a90673 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDSCR_EL1_TDCC ← (( do (pure (_get_MDSCR_EL1_Type_TDCC (← readReg MDSCR_EL1))) ) : SailM (BitVec 1) )
  let __MDCR_EL2_TDCC ← (( do (pure (_get_MDCR_EL2_Type_TDCC (← readReg MDCR_EL2))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDCC ← (( do (pure (_get_MDCR_EL3_Type_TDCC (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  if ((← (Halted ())) : Bool)
  then (X_set t 64 (← (DBGDTR_EL0_read__1 ())))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if ((__MDSCR_EL1_TDCC == 1#1) : Bool)
          then
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              if (((← (EL2Enabled ())) && (__MDCR_EL2_TDCC == 1#1)) : Bool)
              then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do
                         (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2)))))) : Bool)
                  then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                          else (X_set t 64 (← (DBGDTR_EL0_read__1 ()))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
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
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                          else (X_set t 64 (← (DBGDTR_EL0_read__1 ())))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                  then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))
                      else (X_set t 64 (← (DBGDTR_EL0_read__1 ())))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then (X_set t 64 (← (DBGDTR_EL0_read__1 ())))
                  else (pure ())))))

/-- Type quantifiers: t : Int -/
def DBGPRCR_EL1_SysRegRead_cbb37eb996d3a77c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __EDSCR_SDD ← (( do (pure (_get_EDSCR_Type_SDD (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  let __MDCR_EL3_TDOSA ← (( do (pure (_get_MDCR_EL3_Type_TDOSA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __SCR_EL3_FGTEn ← (( do (pure (_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3))) ) : SailM (BitVec 1) )
  let __HDFGRTR_EL2_DBGPRCR_EL1 ← (( do (pure (_get_HDFGRTR_EL2_Type_DBGPRCR_EL1 (← readReg HDFGRTR_EL2))) ) : SailM (BitVec 1) )
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
                       (IsFeatureImplemented FEAT_FGT)))) && ((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1))) && (__HDFGRTR_EL2_DBGPRCR_EL1 == 1#1)) : Bool)
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
                      else (X_set t 64 (__get_DBGPRCR_EL1 (← readReg DBGPRCR_EL1)))))))
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
                  else (X_set t 64 (__get_DBGPRCR_EL1 (← readReg DBGPRCR_EL1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then (X_set t 64 (__get_DBGPRCR_EL1 (← readReg DBGPRCR_EL1)))
              else (pure ()))))


