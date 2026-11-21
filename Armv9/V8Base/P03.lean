import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.ReverseEndianness
import Armv9.Option
import Armv9.MonoRewrites
import Armv9.Common
import Armv9.Prelude
import Armv9.Builtins
import Armv9Core.V8Base

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

def _get_GICC_EOIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_GICC_HPPIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_GICC_IAR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_GICD_CLRSPI_NSR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)

def _get_GICD_CLRSPI_SR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)

def _get_GICD_SETSPI_NSR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)

def _get_GICD_SETSPI_SR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)

def _get_GICD_SGIR_Type_INTID (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_GICM_CLRSPI_NSR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)

def _get_GICM_CLRSPI_SR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)

def _get_GICM_SETSPI_NSR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)

def _get_GICM_SETSPI_SR_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)

def _get_GICM_TYPER_Type_INTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 28 16)

def _get_GICR_INVLPIR_Type_INTID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_GICV_AEOIR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_GICV_AHPPIR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_GICV_AIAR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_GICV_DIR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_GICV_EOIR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_GICV_HPPIR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_GICV_IAR_Type_INTID (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_ICC_ASGI1R_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ICC_ASGI1R_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ICC_DIR_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_DIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_EOIR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_EOIR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_EOIR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_EOIR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_HPPIR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_HPPIR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_HPPIR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_HPPIR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_IAR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_IAR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_IAR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_IAR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_NMIAR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICC_SGI0R_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ICC_SGI0R_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ICC_SGI1R_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ICC_SGI1R_Type_INTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ICV_DIR_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_DIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_EOIR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_EOIR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_EOIR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_EOIR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_HPPIR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_HPPIR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_HPPIR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_HPPIR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_IAR0_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_IAR0_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_IAR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ICV_IAR1_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def undefined_ICH_LR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICH_LR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICH_LR_EL2_Type_Group (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_ICH_LR_EL2_Type_Group (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_ICH_LRC_Type_Group (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_ICH_LRC_Type_Group (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_ICH_LR_EL2_Type_HW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _update_ICH_LR_EL2_Type_HW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_ICH_LRC_Type_HW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_ICH_LRC_Type_HW (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_ICH_LR_EL2_Type_State (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 63 62)

def _update_ICH_LR_EL2_Type_State (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 62 x)

def _update_ICH_LRC_Type_State (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _get_ICH_LRC_Type_State (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)

def _get_ICH_LR_EL2_Type_pINTID (v : (BitVec 64)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 44 32)

def _update_ICH_LR_EL2_Type_pINTID (v : (BitVec 64)) (x : (BitVec 13)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 32 x)

def _update_GICR_CLRLPIR_Type_pINTID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_GICR_SETLPIR_Type_pINTID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_ICH_LRC_Type_pINTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)

def _get_GICR_CLRLPIR_Type_pINTID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_GICR_SETLPIR_Type_pINTID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_ICH_LRC_Type_pINTID (v : (BitVec 32)) : (BitVec 13) :=
  (Sail.BitVec.extractLsb v 12 0)

def _get_ICH_LR_EL2_Type_vINTID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_ICH_LR_EL2_Type_vINTID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_GITS_SGIR_Type_vINTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ICH_LR_Type_vINTID (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_GITS_SGIR_Type_vINTID (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ICH_LR_Type_vINTID (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def undefined_MVFR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MVFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MVFR0_EL1_Type_FPDP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_MVFR0_EL1_Type_FPDP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_MVFR0_Type_FPDP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_MVFR0_EL1_Type_FPDivide (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_MVFR0_EL1_Type_FPDivide (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_MVFR0_Type_FPDivide (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_MVFR0_EL1_Type_FPRound (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_MVFR0_EL1_Type_FPRound (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_MVFR0_Type_FPRound (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_MVFR0_EL1_Type_FPSP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_MVFR0_EL1_Type_FPSP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_MVFR0_Type_FPSP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_MVFR0_EL1_Type_FPShVec (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_MVFR0_EL1_Type_FPShVec (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_MVFR0_Type_FPShVec (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_MVFR0_EL1_Type_FPSqrt (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_MVFR0_EL1_Type_FPSqrt (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_MVFR0_Type_FPSqrt (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_MVFR0_EL1_Type_FPTrap (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_MVFR0_EL1_Type_FPTrap (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_MVFR0_Type_FPTrap (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_MVFR0_EL1_Type_SIMDReg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_MVFR0_EL1_Type_SIMDReg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_MVFR0_Type_SIMDReg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def undefined_ICC_HPPIR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_HPPIR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_AA64DFR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64DFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64DFR0_EL1_Type_BRBE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64DFR0_EL1_Type_BRBE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_ID_AA64DFR0_EL1_Type_BRPs (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_DBGDIDR_Type_BRPs (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_EDDFR1_Type_BRPs (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_EDDFR_Type_BRPs (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_AA64DFR1_EL1_Type_BRPs (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _get_DBGDIDR_Type_BRPs (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_EDDFR1_Type_BRPs (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_EDDFR_Type_BRPs (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_AA64DFR1_EL1_Type_BRPs (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _update_ID_AA64DFR0_EL1_Type_CTX_CMPs (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_DBGDIDR_Type_CTX_CMPs (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_EDDFR1_Type_CTX_CMPs (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_EDDFR_Type_CTX_CMPs (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_AA64DFR1_EL1_Type_CTX_CMPs (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _get_DBGDIDR_Type_CTX_CMPs (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_EDDFR1_Type_CTX_CMPs (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_EDDFR_Type_CTX_CMPs (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_AA64DFR1_EL1_Type_CTX_CMPs (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_ID_AA64DFR0_EL1_Type_DebugVer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_AA64DFR0_EL1_Type_DebugVer (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_AA64DFR0_EL1_Type_DoubleLock (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _update_ID_AA64DFR0_EL1_Type_DoubleLock (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_DBGDEVID_Type_DoubleLock (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_DBGDEVID_Type_DoubleLock (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_AA64DFR0_EL1_Type_ExtTrcBuff (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _update_ID_AA64DFR0_EL1_Type_ExtTrcBuff (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_EDDFR_Type_ExtTrcBuff (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _get_EDDFR_Type_ExtTrcBuff (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_ID_AA64DFR0_EL1_Type_HPMN0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _update_ID_AA64DFR0_EL1_Type_HPMN0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_ID_DFR1_EL1_Type_HPMN0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_DFR1_Type_HPMN0 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_DFR1_EL1_Type_HPMN0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_DFR1_Type_HPMN0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_AA64DFR0_EL1_Type_MTPMU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _update_ID_AA64DFR0_EL1_Type_MTPMU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_ID_DFR1_EL1_Type_MTPMU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_DFR1_EL1_Type_MTPMU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_DFR1_Type_MTPMU (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_AA64DFR0_EL1_Type_PMSS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64DFR0_EL1_Type_PMSS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_EDDFR_Type_PMSS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_PMDEVID_Type_PMSS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_EDDFR_Type_PMSS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_PMDEVID_Type_PMSS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_AA64DFR0_EL1_Type_PMSVer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_ID_AA64DFR0_EL1_Type_PMSVer (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_ID_AA64DFR0_EL1_Type_PMUVer (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_EDDFR_Type_PMUVer (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_EDDFR_Type_PMUVer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_AA64DFR0_EL1_Type_SEBEP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_AA64DFR0_EL1_Type_SEBEP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_EDDFR_Type_SEBEP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_EDDFR_Type_SEBEP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_AA64DFR0_EL1_Type_TraceBuffer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _update_ID_AA64DFR0_EL1_Type_TraceBuffer (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ID_AA64DFR0_EL1_Type_TraceFilt (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_EDDFR_Type_TraceFilt (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_ID_DFR0_EL1_Type_TraceFilt (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_EDDFR_Type_TraceFilt (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_ID_DFR0_EL1_Type_TraceFilt (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_DFR0_Type_TraceFilt (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_AA64DFR0_EL1_Type_TraceVer (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_EDDFR_Type_TraceVer (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_EDDFR_Type_TraceVer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_AA64DFR0_EL1_Type_WRPs (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_DBGDIDR_Type_WRPs (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_EDDFR1_Type_WRPs (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_EDDFR_Type_WRPs (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_AA64DFR1_EL1_Type_WRPs (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _get_DBGDIDR_Type_WRPs (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_EDDFR1_Type_WRPs (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_EDDFR_Type_WRPs (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_AA64DFR1_EL1_Type_WRPs (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def undefined_ICV_BPR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_BPR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICV_BPR1_EL1_Type_BinaryPoint (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _update_ICV_BPR1_EL1_Type_BinaryPoint (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_ICC_BPR0_EL1_Type_BinaryPoint (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_ICC_BPR0_Type_BinaryPoint (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_ICC_BPR1_EL1_Type_BinaryPoint (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_ICC_BPR1_Type_BinaryPoint (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_ICV_BPR0_EL1_Type_BinaryPoint (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_ICV_BPR0_Type_BinaryPoint (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_ICV_BPR1_Type_BinaryPoint (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _get_ICC_BPR0_EL1_Type_BinaryPoint (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_ICC_BPR0_Type_BinaryPoint (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_ICC_BPR1_EL1_Type_BinaryPoint (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_ICC_BPR1_Type_BinaryPoint (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_ICV_BPR0_EL1_Type_BinaryPoint (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_ICV_BPR0_Type_BinaryPoint (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_ICV_BPR1_Type_BinaryPoint (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def undefined_ID_ISAR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_ISAR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_ISAR2_EL1_Type_LoadStore (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_ISAR2_EL1_Type_LoadStore (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_ISAR2_Type_LoadStore (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_ISAR2_EL1_Type_MemHint (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_ISAR2_EL1_Type_MemHint (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_ISAR2_Type_MemHint (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_ISAR2_EL1_Type_Mult (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_ISAR2_EL1_Type_Mult (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_ISAR2_Type_Mult (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_ISAR2_EL1_Type_MultS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_ISAR2_EL1_Type_MultS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_ISAR2_Type_MultS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_ISAR2_EL1_Type_MultU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_ISAR2_EL1_Type_MultU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_ISAR2_Type_MultU (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_ISAR2_EL1_Type_MultiAccessInt (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_ISAR2_EL1_Type_MultiAccessInt (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_ISAR2_Type_MultiAccessInt (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_ISAR2_EL1_Type_PSR_AR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_ISAR2_EL1_Type_PSR_AR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_ISAR2_Type_PSR_AR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_ISAR2_EL1_Type_Reversal (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_ISAR2_EL1_Type_Reversal (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_ISAR2_Type_Reversal (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def undefined_PMECR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMECR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMECR_EL1_Type_KPME (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_PMECR_EL1_Type_KPME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_PMECR_EL1_Type_SSE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 4 3)

def _update_PMECR_EL1_Type_SSE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 3 x)

def undefined_ICV_EOIR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_EOIR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_RMR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_RMR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_RMR_EL1_Type_AA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_RMR_EL1_Type_AA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HRMR_Type_AA64 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_RMR_EL2_Type_AA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_RMR_EL3_Type_AA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_RMR_Type_AA64 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_HRMR_Type_AA64 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_RMR_EL2_Type_AA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_RMR_EL3_Type_AA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_RMR_Type_AA64 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_RMR_EL1_Type_RR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_RMR_EL1_Type_RR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_RMR_EL2_Type_RR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_RMR_EL3_Type_RR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_HRMR_Type_RR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_RMR_EL2_Type_RR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_RMR_EL3_Type_RR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_RMR_Type_RR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def undefined_OSLAR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_OSLAR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICC_HPPIR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_HPPIR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def __set_CNTHPS_CTL_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTHPS_CTL_EL2_Type := value_name
  writeReg CNTHPS_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHPS_CTL_EL2) 1 0 (BitVec.slice r 0 2))
  writeReg CNTHPS_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHPS_CTL_EL2) 63 3 (BitVec.slice r 3 61))

def undefined_HAFGRTR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HAFGRTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HAFGRTR_EL2_Type_AMCNTEN0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_HAFGRTR_EL2_Type_AMCNTEN0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_HAFGRTR_EL2_Type_AMCNTEN1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_HAFGRTR_EL2_Type_AMCNTEN1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_HAFGRTR_EL2_Type_AMEVCNTR00_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_HAFGRTR_EL2_Type_AMEVCNTR00_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_HAFGRTR_EL2_Type_AMEVCNTR01_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_HAFGRTR_EL2_Type_AMEVCNTR01_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_HAFGRTR_EL2_Type_AMEVCNTR02_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_HAFGRTR_EL2_Type_AMEVCNTR02_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_HAFGRTR_EL2_Type_AMEVCNTR03_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_HAFGRTR_EL2_Type_AMEVCNTR03_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_HAFGRTR_EL2_Type_AMEVCNTR10_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_HAFGRTR_EL2_Type_AMEVCNTR10_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR10_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR10_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_HAFGRTR_EL2_Type_AMEVCNTR110_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)

def _update_HAFGRTR_EL2_Type_AMEVCNTR110_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR110_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR110_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_HAFGRTR_EL2_Type_AMEVCNTR111_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _update_HAFGRTR_EL2_Type_AMEVCNTR111_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR111_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR111_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_HAFGRTR_EL2_Type_AMEVCNTR112_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)

def _update_HAFGRTR_EL2_Type_AMEVCNTR112_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR112_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR112_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_HAFGRTR_EL2_Type_AMEVCNTR113_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _update_HAFGRTR_EL2_Type_AMEVCNTR113_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR113_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR113_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_HAFGRTR_EL2_Type_AMEVCNTR114_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _update_HAFGRTR_EL2_Type_AMEVCNTR114_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR114_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR114_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_HAFGRTR_EL2_Type_AMEVCNTR115_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_HAFGRTR_EL2_Type_AMEVCNTR115_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR115_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR115_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_HAFGRTR_EL2_Type_AMEVCNTR11_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_HAFGRTR_EL2_Type_AMEVCNTR11_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR11_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR11_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_HAFGRTR_EL2_Type_AMEVCNTR12_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_HAFGRTR_EL2_Type_AMEVCNTR12_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR12_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR12_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_HAFGRTR_EL2_Type_AMEVCNTR13_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_HAFGRTR_EL2_Type_AMEVCNTR13_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR13_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR13_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_HAFGRTR_EL2_Type_AMEVCNTR14_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_HAFGRTR_EL2_Type_AMEVCNTR14_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR14_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR14_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_HAFGRTR_EL2_Type_AMEVCNTR15_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_HAFGRTR_EL2_Type_AMEVCNTR15_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR15_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR15_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_HAFGRTR_EL2_Type_AMEVCNTR16_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_HAFGRTR_EL2_Type_AMEVCNTR16_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR16_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR16_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_HAFGRTR_EL2_Type_AMEVCNTR17_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_HAFGRTR_EL2_Type_AMEVCNTR17_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR17_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR17_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_HAFGRTR_EL2_Type_AMEVCNTR18_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _update_HAFGRTR_EL2_Type_AMEVCNTR18_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR18_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR18_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_HAFGRTR_EL2_Type_AMEVCNTR19_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_HAFGRTR_EL2_Type_AMEVCNTR19_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_AMCG1IDR_EL0_Type_AMEVCNTR19_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTR19_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_HAFGRTR_EL2_Type_AMEVTYPER10_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_HAFGRTR_EL2_Type_AMEVTYPER10_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER110_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _update_HAFGRTR_EL2_Type_AMEVTYPER110_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER111_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _update_HAFGRTR_EL2_Type_AMEVTYPER111_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER112_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _update_HAFGRTR_EL2_Type_AMEVTYPER112_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER113_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _update_HAFGRTR_EL2_Type_AMEVTYPER113_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER114_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _update_HAFGRTR_EL2_Type_AMEVTYPER114_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER115_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _update_HAFGRTR_EL2_Type_AMEVTYPER115_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER11_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_HAFGRTR_EL2_Type_AMEVTYPER11_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER12_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_HAFGRTR_EL2_Type_AMEVTYPER12_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER13_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_HAFGRTR_EL2_Type_AMEVTYPER13_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER14_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_HAFGRTR_EL2_Type_AMEVTYPER14_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER15_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_HAFGRTR_EL2_Type_AMEVTYPER15_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER16_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_HAFGRTR_EL2_Type_AMEVTYPER16_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER17_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_HAFGRTR_EL2_Type_AMEVTYPER17_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER18_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _update_HAFGRTR_EL2_Type_AMEVTYPER18_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _get_HAFGRTR_EL2_Type_AMEVTYPER19_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_HAFGRTR_EL2_Type_AMEVTYPER19_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def undefined_ICC_BPR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_BPR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_AA64DFR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64DFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64DFR1_EL1_Type_ABLE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _update_ID_AA64DFR1_EL1_Type_ABLE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_EDDFR1_Type_ABLE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _get_EDDFR1_Type_ABLE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_ID_AA64DFR1_EL1_Type_ABL_CMPs (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _update_ID_AA64DFR1_EL1_Type_ABL_CMPs (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _update_EDDFR1_Type_ABL_CMPs (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _get_EDDFR1_Type_ABL_CMPs (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _get_ID_AA64DFR1_EL1_Type_DPFZS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64DFR1_EL1_Type_DPFZS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _get_ID_AA64DFR1_EL1_Type_EBEP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _update_ID_AA64DFR1_EL1_Type_EBEP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_EDDFR1_Type_EBEP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _get_EDDFR1_Type_EBEP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_ID_AA64DFR1_EL1_Type_PMICNTR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _update_ID_AA64DFR1_EL1_Type_PMICNTR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_EDDFR1_Type_PMICNTR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _get_EDDFR1_Type_PMICNTR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_ID_AA64DFR1_EL1_Type_SPMU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_ID_AA64DFR1_EL1_Type_SPMU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_EDDFR1_Type_SPMU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_EDDFR1_Type_SPMU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_ID_AA64DFR1_EL1_Type_SYSPMUID (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_ID_AA64DFR1_EL1_Type_SYSPMUID (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_EDDFR1_Type_SYSPMUID (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_EDDFR1_Type_SYSPMUID (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def undefined_ACCDATA_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ACCDATA_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ACCDATA_EL1_Type_ACCDATA (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_ACCDATA_EL1_Type_ACCDATA (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def undefined_PMSSCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSSCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMSSCR_EL1_Type_NC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_PMSSCR_EL1_Type_NC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def undefined_LORID_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_LORID_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_LORID_EL1_Type_LR (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_LORID_EL1_Type_LR (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def undefined_CNTP_TVAL_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTP_TVAL_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_CNTP_TVAL_EL0_Type_TimerValue (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_CNTP_TVAL_EL0_Type_TimerValue (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_CNTHPS_TVAL_EL2_Type_TimerValue (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_CNTHP_TVAL_EL2_Type_TimerValue (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_CNTHVS_TVAL_EL2_Type_TimerValue (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_CNTHV_TVAL_EL2_Type_TimerValue (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_CNTPS_TVAL_EL1_Type_TimerValue (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_CNTV_TVAL_EL0_Type_TimerValue (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_CNTHPS_TVAL_EL2_Type_TimerValue (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_CNTHP_TVAL_EL2_Type_TimerValue (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_CNTHVS_TVAL_EL2_Type_TimerValue (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_CNTHV_TVAL_EL2_Type_TimerValue (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_CNTPS_TVAL_EL1_Type_TimerValue (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_CNTV_TVAL_EL0_Type_TimerValue (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def undefined_ID_AA64ISAR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64ISAR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64ISAR1_EL1_Type_APA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_AA64ISAR1_EL1_Type_APA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_AA64ISAR1_EL1_Type_BF16 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _update_ID_AA64ISAR1_EL1_Type_BF16 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ID_AA64ZFR0_EL1_Type_BF16 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_ISAR6_EL1_Type_BF16 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_AA64ZFR0_EL1_Type_BF16 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_ISAR6_EL1_Type_BF16 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_ISAR6_Type_BF16 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_AA64ISAR1_EL1_Type_DGH (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _update_ID_AA64ISAR1_EL1_Type_DGH (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _get_ID_AA64ISAR1_EL1_Type_DPB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_AA64ISAR1_EL1_Type_DPB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_AA64ISAR1_EL1_Type_FCMA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64ISAR1_EL1_Type_FCMA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_AA64ISAR1_EL1_Type_FRINTTS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_ID_AA64ISAR1_EL1_Type_FRINTTS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_ID_AA64ISAR1_EL1_Type_GPA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_AA64ISAR1_EL1_Type_GPA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_AA64ISAR1_EL1_Type_GPI (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_AA64ISAR1_EL1_Type_GPI (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_AA64ISAR1_EL1_Type_I8MM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64ISAR1_EL1_Type_I8MM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_ID_AA64ZFR0_EL1_Type_I8MM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ID_ISAR6_EL1_Type_I8MM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_AA64ZFR0_EL1_Type_I8MM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_ID_ISAR6_EL1_Type_I8MM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_ISAR6_Type_I8MM (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_AA64ISAR1_EL1_Type_JSCVT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_AA64ISAR1_EL1_Type_JSCVT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_ISAR6_EL1_Type_JSCVT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_ISAR6_EL1_Type_JSCVT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_ISAR6_Type_JSCVT (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_AA64ISAR1_EL1_Type_LRCPC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_AA64ISAR1_EL1_Type_LRCPC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_AA64ISAR1_EL1_Type_LS64 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _update_ID_AA64ISAR1_EL1_Type_LS64 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _get_ID_AA64ISAR1_EL1_Type_SB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _update_ID_AA64ISAR1_EL1_Type_SB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_ID_ISAR6_EL1_Type_SB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_ISAR6_Type_SB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_ISAR6_EL1_Type_SB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_ISAR6_Type_SB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_AA64ISAR1_EL1_Type_SPECRES (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _update_ID_AA64ISAR1_EL1_Type_SPECRES (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_ID_ISAR6_EL1_Type_SPECRES (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_ISAR6_EL1_Type_SPECRES (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_ISAR6_Type_SPECRES (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_AA64ISAR1_EL1_Type_XS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _update_ID_AA64ISAR1_EL1_Type_XS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def undefined_ID_AA64MMFR4_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64MMFR4_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64MMFR4_EL1_Type_EIESB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_AA64MMFR4_EL1_Type_EIESB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def undefined_ICH_EISR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICH_EISR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICH_EISR_EL2_Type_Status0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_ICH_EISR_EL2_Type_Status0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICH_EISR_Type_Status0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICH_ELRSR_Type_Status0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_ELRSR_EL2_Type_Status0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_ELRSR_Type_Status0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICH_EISR_Type_Status0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_GICH_ELRSR_Type_Status0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_EISR_Type_Status0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_ELRSR_EL2_Type_Status0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_ELRSR_Type_Status0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_EISR_EL2_Type_Status1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_ICH_EISR_EL2_Type_Status1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GICH_EISR_Type_Status1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GICH_ELRSR_Type_Status1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_ELRSR_EL2_Type_Status1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_ELRSR_Type_Status1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GICH_EISR_Type_Status1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_GICH_ELRSR_Type_Status1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_EISR_Type_Status1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_ELRSR_EL2_Type_Status1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_ELRSR_Type_Status1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_EISR_EL2_Type_Status10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_ICH_EISR_EL2_Type_Status10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_GICH_EISR_Type_Status10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_GICH_ELRSR_Type_Status10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_ICH_ELRSR_EL2_Type_Status10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_ICH_ELRSR_Type_Status10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_GICH_EISR_Type_Status10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_GICH_ELRSR_Type_Status10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_ICH_EISR_Type_Status10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_ICH_ELRSR_EL2_Type_Status10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_ICH_ELRSR_Type_Status10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_ICH_EISR_EL2_Type_Status11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_ICH_EISR_EL2_Type_Status11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_GICH_EISR_Type_Status11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_GICH_ELRSR_Type_Status11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_ICH_ELRSR_EL2_Type_Status11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_ICH_ELRSR_Type_Status11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_GICH_EISR_Type_Status11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_GICH_ELRSR_Type_Status11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_ICH_EISR_Type_Status11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_ICH_ELRSR_EL2_Type_Status11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_ICH_ELRSR_Type_Status11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_ICH_EISR_EL2_Type_Status12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_ICH_EISR_EL2_Type_Status12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_GICH_EISR_Type_Status12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_GICH_ELRSR_Type_Status12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ICH_ELRSR_EL2_Type_Status12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ICH_ELRSR_Type_Status12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_GICH_EISR_Type_Status12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_GICH_ELRSR_Type_Status12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_ICH_EISR_Type_Status12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_ICH_ELRSR_EL2_Type_Status12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_ICH_ELRSR_Type_Status12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_ICH_EISR_EL2_Type_Status13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_ICH_EISR_EL2_Type_Status13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_GICH_EISR_Type_Status13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_GICH_ELRSR_Type_Status13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_ICH_ELRSR_EL2_Type_Status13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_ICH_ELRSR_Type_Status13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_GICH_EISR_Type_Status13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_GICH_ELRSR_Type_Status13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_ICH_EISR_Type_Status13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_ICH_ELRSR_EL2_Type_Status13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_ICH_ELRSR_Type_Status13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_ICH_EISR_EL2_Type_Status14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_ICH_EISR_EL2_Type_Status14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_GICH_EISR_Type_Status14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_GICH_ELRSR_Type_Status14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICH_ELRSR_EL2_Type_Status14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICH_ELRSR_Type_Status14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_GICH_EISR_Type_Status14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_GICH_ELRSR_Type_Status14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICH_EISR_Type_Status14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICH_ELRSR_EL2_Type_Status14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICH_ELRSR_Type_Status14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICH_EISR_EL2_Type_Status15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_ICH_EISR_EL2_Type_Status15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_GICH_EISR_Type_Status15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_GICH_ELRSR_Type_Status15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICH_ELRSR_EL2_Type_Status15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICH_ELRSR_Type_Status15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_GICH_EISR_Type_Status15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_GICH_ELRSR_Type_Status15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICH_EISR_Type_Status15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICH_ELRSR_EL2_Type_Status15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICH_ELRSR_Type_Status15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICH_EISR_EL2_Type_Status2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_ICH_EISR_EL2_Type_Status2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_GICH_EISR_Type_Status2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_GICH_ELRSR_Type_Status2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICH_ELRSR_EL2_Type_Status2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICH_ELRSR_Type_Status2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GICH_EISR_Type_Status2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_GICH_ELRSR_Type_Status2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_EISR_Type_Status2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_ELRSR_EL2_Type_Status2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_ELRSR_Type_Status2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_EISR_EL2_Type_Status3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_ICH_EISR_EL2_Type_Status3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GICH_EISR_Type_Status3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GICH_ELRSR_Type_Status3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICH_ELRSR_EL2_Type_Status3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICH_ELRSR_Type_Status3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_GICH_EISR_Type_Status3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_GICH_ELRSR_Type_Status3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_EISR_Type_Status3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_ELRSR_EL2_Type_Status3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_ELRSR_Type_Status3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_EISR_EL2_Type_Status4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_ICH_EISR_EL2_Type_Status4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_GICH_EISR_Type_Status4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_GICH_ELRSR_Type_Status4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICH_ELRSR_EL2_Type_Status4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICH_ELRSR_Type_Status4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_GICH_EISR_Type_Status4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_GICH_ELRSR_Type_Status4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_EISR_Type_Status4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_ELRSR_EL2_Type_Status4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_ELRSR_Type_Status4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_EISR_EL2_Type_Status5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_ICH_EISR_EL2_Type_Status5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_GICH_EISR_Type_Status5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_GICH_ELRSR_Type_Status5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ICH_ELRSR_EL2_Type_Status5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ICH_ELRSR_Type_Status5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_GICH_EISR_Type_Status5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_GICH_ELRSR_Type_Status5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_EISR_Type_Status5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_ELRSR_EL2_Type_Status5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_ELRSR_Type_Status5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_EISR_EL2_Type_Status6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_ICH_EISR_EL2_Type_Status6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_GICH_EISR_Type_Status6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_GICH_ELRSR_Type_Status6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICH_ELRSR_EL2_Type_Status6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICH_ELRSR_Type_Status6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_GICH_EISR_Type_Status6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_GICH_ELRSR_Type_Status6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_EISR_Type_Status6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_ELRSR_EL2_Type_Status6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_ELRSR_Type_Status6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_EISR_EL2_Type_Status7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_ICH_EISR_EL2_Type_Status7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_GICH_EISR_Type_Status7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_GICH_ELRSR_Type_Status7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ICH_ELRSR_EL2_Type_Status7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ICH_ELRSR_Type_Status7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_GICH_EISR_Type_Status7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_GICH_ELRSR_Type_Status7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_EISR_Type_Status7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_ELRSR_EL2_Type_Status7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_ELRSR_Type_Status7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_EISR_EL2_Type_Status8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_ICH_EISR_EL2_Type_Status8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_GICH_EISR_Type_Status8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_GICH_ELRSR_Type_Status8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_ICH_ELRSR_EL2_Type_Status8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_ICH_ELRSR_Type_Status8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_GICH_EISR_Type_Status8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_GICH_ELRSR_Type_Status8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_ICH_EISR_Type_Status8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_ICH_ELRSR_EL2_Type_Status8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_ICH_ELRSR_Type_Status8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_ICH_EISR_EL2_Type_Status9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_ICH_EISR_EL2_Type_Status9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_GICH_EISR_Type_Status9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_GICH_ELRSR_Type_Status9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ICH_ELRSR_EL2_Type_Status9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ICH_ELRSR_Type_Status9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_GICH_EISR_Type_Status9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_GICH_ELRSR_Type_Status9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICH_EISR_Type_Status9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICH_ELRSR_EL2_Type_Status9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICH_ELRSR_Type_Status9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def undefined_MIDR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MIDR_EL1_Type_Architecture (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_MIDR_EL1_Type_Architecture (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_VPIDR_EL2_Type_Architecture (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_MIDR_Type_Architecture (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_VPIDR_EL2_Type_Architecture (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_VPIDR_Type_Architecture (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_MIDR_EL1_Type_Implementer (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _update_MIDR_EL1_Type_Implementer (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_AMIIDR_Type_Implementer (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 0 x)

def _update_FPSID_Type_Implementer (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_GICD_IIDR_Type_Implementer (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 0 x)

def _update_GICM_IIDR_Type_Implementer (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 0 x)

def _update_GICR_IIDR_Type_Implementer (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 0 x)

def _update_GITS_IIDR_Type_Implementer (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 0 x)

def _update_SMIDR_EL1_Type_Implementer (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_VPIDR_EL2_Type_Implementer (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _get_AMIIDR_Type_Implementer (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 11 0)

def _get_FPSID_Type_Implementer (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_GICD_IIDR_Type_Implementer (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 11 0)

def _get_GICM_IIDR_Type_Implementer (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 11 0)

def _get_GICR_IIDR_Type_Implementer (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 11 0)

def _get_GITS_IIDR_Type_Implementer (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 11 0)

def _get_MIDR_Type_Implementer (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_SMIDR_EL1_Type_Implementer (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_VPIDR_EL2_Type_Implementer (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_VPIDR_Type_Implementer (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_MIDR_EL1_Type_PartNum (v : (BitVec 64)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 15 4)

def _update_MIDR_EL1_Type_PartNum (v : (BitVec 64)) (x : (BitVec 12)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 4 x)

def _update_FPSID_Type_PartNum (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_VPIDR_EL2_Type_PartNum (v : (BitVec 64)) (x : (BitVec 12)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 4 x)

def _get_FPSID_Type_PartNum (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MIDR_Type_PartNum (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 15 4)

def _get_VPIDR_EL2_Type_PartNum (v : (BitVec 64)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 15 4)

def _get_VPIDR_Type_PartNum (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 15 4)

def _get_MIDR_EL1_Type_Revision (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_MIDR_EL1_Type_Revision (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_AMIIDR_Type_Revision (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_FPSID_Type_Revision (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_GICD_IIDR_Type_Revision (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_GICM_IIDR_Type_Revision (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_GICR_IIDR_Type_Revision (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_GITS_IIDR_Type_Revision (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_PMIIDR_Type_Revision (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_SMIDR_EL1_Type_Revision (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_VPIDR_EL2_Type_Revision (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_AMIIDR_Type_Revision (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_FPSID_Type_Revision (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_GICD_IIDR_Type_Revision (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_GICM_IIDR_Type_Revision (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_GICR_IIDR_Type_Revision (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_GITS_IIDR_Type_Revision (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_MIDR_Type_Revision (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PMIIDR_Type_Revision (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_SMIDR_EL1_Type_Revision (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_VPIDR_EL2_Type_Revision (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_VPIDR_Type_Revision (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_MIDR_EL1_Type_Variant (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_MIDR_EL1_Type_Variant (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_AMIIDR_Type_Variant (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_FPSID_Type_Variant (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_GICD_IIDR_Type_Variant (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_GICM_IIDR_Type_Variant (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_GICR_IIDR_Type_Variant (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_GITS_IIDR_Type_Variant (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_PMIIDR_Type_Variant (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_VPIDR_EL2_Type_Variant (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_AMIIDR_Type_Variant (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_FPSID_Type_Variant (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_GICD_IIDR_Type_Variant (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_GICM_IIDR_Type_Variant (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_GICR_IIDR_Type_Variant (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_GITS_IIDR_Type_Variant (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_MIDR_Type_Variant (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_PMIIDR_Type_Variant (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_VPIDR_EL2_Type_Variant (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_VPIDR_Type_Variant (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def undefined_ICC_RPR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_RPR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICC_RPR_EL1_Type_NMI_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_ICC_RPR_EL1_Type_NMI_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def undefined_ICH_ELRSR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICH_ELRSR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICC_SGI0R_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_SGI0R_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICC_SGI0R_EL1_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _update_ICC_SGI0R_EL1_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_GITS_MPIDR_Type_Aff1 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_ICC_ASGI1R_EL1_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_ICC_ASGI1R_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_ICC_SGI0R_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_ICC_SGI1R_EL1_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_ICC_SGI1R_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MPIDR_EL1_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_VMPIDR_EL2_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _get_GITS_MPIDR_Type_Aff1 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_ICC_ASGI1R_EL1_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_ICC_ASGI1R_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_ICC_SGI0R_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_ICC_SGI1R_EL1_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_ICC_SGI1R_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MPIDR_EL1_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MPIDR_Type_Aff1 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_VMPIDR_EL2_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_VMPIDR_Type_Aff1 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_ICC_SGI0R_EL1_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _update_ICC_SGI0R_EL1_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_GITS_MPIDR_Type_Aff2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_ICC_ASGI1R_EL1_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_ICC_ASGI1R_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_ICC_SGI0R_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_ICC_SGI1R_EL1_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_ICC_SGI1R_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_MPIDR_EL1_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_VMPIDR_EL2_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _get_GITS_MPIDR_Type_Aff2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_ICC_ASGI1R_EL1_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_ICC_ASGI1R_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_ICC_SGI0R_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_ICC_SGI1R_EL1_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_ICC_SGI1R_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_MPIDR_EL1_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MPIDR_Type_Aff2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_VMPIDR_EL2_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_VMPIDR_Type_Aff2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_ICC_SGI0R_EL1_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _update_ICC_SGI0R_EL1_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_GITS_MPIDR_Type_Aff3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_ICC_ASGI1R_EL1_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_ICC_ASGI1R_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_ICC_SGI0R_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_ICC_SGI1R_EL1_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_ICC_SGI1R_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_MPIDR_EL1_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_VMPIDR_EL2_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _get_GITS_MPIDR_Type_Aff3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_ICC_ASGI1R_EL1_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_ICC_ASGI1R_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_ICC_SGI0R_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_ICC_SGI1R_EL1_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_ICC_SGI1R_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_MPIDR_EL1_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_VMPIDR_EL2_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_ICC_SGI0R_EL1_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _update_ICC_SGI0R_EL1_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_ICC_ASGI1R_EL1_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_ICC_ASGI1R_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_ICC_SGI0R_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_ICC_SGI1R_EL1_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_ICC_SGI1R_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _get_ICC_ASGI1R_EL1_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _get_ICC_ASGI1R_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _get_ICC_SGI0R_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _get_ICC_SGI1R_EL1_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _get_ICC_SGI1R_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _get_ICC_SGI0R_EL1_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _update_ICC_SGI0R_EL1_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ICC_ASGI1R_EL1_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ICC_ASGI1R_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ICC_SGI0R_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ICC_SGI1R_EL1_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ICC_SGI1R_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _get_ICC_ASGI1R_EL1_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_ICC_ASGI1R_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_ICC_SGI0R_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_ICC_SGI1R_EL1_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_ICC_SGI1R_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_ICC_SGI0R_EL1_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_ICC_SGI0R_EL1_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_ICC_ASGI1R_EL1_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_ICC_ASGI1R_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_ICC_SGI0R_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_ICC_SGI1R_EL1_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_ICC_SGI1R_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_ICC_ASGI1R_EL1_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_ICC_ASGI1R_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_ICC_SGI0R_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_ICC_SGI1R_EL1_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_ICC_SGI1R_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def __set_CNTHVS_CTL_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTHVS_CTL_EL2_Type := value_name
  writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHVS_CTL_EL2) 1 0 (BitVec.slice r 0 2))
  writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHVS_CTL_EL2) 63 3 (BitVec.slice r 3 61))

def undefined_SPMACCESSR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPMACCESSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SPMACCESSR_EL1_Type_P31 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 63 62)

def _update_SPMACCESSR_EL1_Type_P31 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 62 x)

def _update_ICH_AP0R_EL2_Type_P31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_ICH_AP0R_Type_P31 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_ICH_AP1R_EL2_Type_P31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_ICH_AP1R_Type_P31 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SPMACCESSR_EL2_Type_P31 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 62 x)

def _update_SPMACCESSR_EL3_Type_P31 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 62 x)

def _get_ICH_AP0R_EL2_Type_P31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_ICH_AP0R_Type_P31 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_ICH_AP1R_EL2_Type_P31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_ICH_AP1R_Type_P31 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPMACCESSR_EL2_Type_P31 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 63 62)

def _get_SPMACCESSR_EL3_Type_P31 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 63 62)

def undefined_SPMSELR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPMSELR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SPMSELR_EL0_Type_SYSPMUSEL (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 9 4)

def _update_SPMSELR_EL0_Type_SYSPMUSEL (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 4 x)

def undefined_ID_AA64PFR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64PFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64PFR1_EL1_Type_CSV2_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_ID_AA64PFR1_EL1_Type_CSV2_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_ID_AA64PFR1_EL1_Type_DF2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _update_ID_AA64PFR1_EL1_Type_DF2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _get_ID_AA64PFR1_EL1_Type_GCS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _update_ID_AA64PFR1_EL1_Type_GCS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_EDHSR_Type_GCS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _get_EDHSR_Type_GCS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _update_ID_AA64PFR1_EL1_Type_MPAM_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_AA64PFR1_EL1_Type_MTE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_AA64PFR1_EL1_Type_MTE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_AA64PFR1_EL1_Type_MTEX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64PFR1_EL1_Type_MTEX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _get_ID_AA64PFR1_EL1_Type_MTE_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _update_ID_AA64PFR1_EL1_Type_MTE_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _get_ID_AA64PFR1_EL1_Type_PFAR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _update_ID_AA64PFR1_EL1_Type_PFAR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _get_ID_AA64PFR1_EL1_Type_RAS_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_AA64PFR1_EL1_Type_RAS_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_PFR2_EL1_Type_RAS_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_PFR2_Type_RAS_frac (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_PFR2_EL1_Type_RAS_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_PFR2_Type_RAS_frac (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_AA64PFR1_EL1_Type_RNDR_trap (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_AA64PFR1_EL1_Type_RNDR_trap (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_AA64PFR1_EL1_Type_SME (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_AA64PFR1_EL1_Type_SME (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_AA64PFR1_EL1_Type_THE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _update_ID_AA64PFR1_EL1_Type_THE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def undefined_ID_AA64PFR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64PFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64PFR0_EL1_Type_AMU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _update_ID_AA64PFR0_EL1_Type_AMU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_EDPFR_Type_AMU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ID_PFR0_EL1_Type_AMU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_EDPFR_Type_AMU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_ID_PFR0_EL1_Type_AMU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_PFR0_Type_AMU (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_AA64PFR0_EL1_Type_AdvSIMD (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_EDPFR_Type_AdvSIMD (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_EDPFR_Type_AdvSIMD (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_AA64PFR0_EL1_Type_CSV2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _update_ID_AA64PFR0_EL1_Type_CSV2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_ID_PFR0_EL1_Type_CSV2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_PFR0_EL1_Type_CSV2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_PFR0_Type_CSV2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_AA64PFR0_EL1_Type_CSV3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _update_ID_AA64PFR0_EL1_Type_CSV3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_ID_PFR2_EL1_Type_CSV3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_PFR2_Type_CSV3 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_PFR2_EL1_Type_CSV3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_PFR2_Type_CSV3 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_AA64PFR0_EL1_Type_EL0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_EDPFR_Type_EL0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_EDPFR_Type_EL0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_AA64PFR0_EL1_Type_EL1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_EDPFR_Type_EL1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_EDPFR_Type_EL1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_AA64PFR0_EL1_Type_EL2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_EDAA32PFR_Type_EL2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_EDPFR_Type_EL2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_EDAA32PFR_Type_EL2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_EDPFR_Type_EL2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_AA64PFR0_EL1_Type_EL3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_EDAA32PFR_Type_EL3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_EDPFR_Type_EL3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_EDAA32PFR_Type_EL3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_EDPFR_Type_EL3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_AA64PFR0_EL1_Type_FP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64PFR0_EL1_Type_FP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_EDPFR_Type_FP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_EDPFR_Type_FP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64PFR0_EL1_Type_GIC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_EDPFR_Type_GIC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_PFR1_EL1_Type_GIC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_EDPFR_Type_GIC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_PFR1_EL1_Type_GIC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_PFR1_Type_GIC (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_AA64PFR0_EL1_Type_MPAM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_GITS_TYPER_Type_MPAM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _get_GITS_TYPER_Type_MPAM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)

def _get_ID_AA64PFR0_EL1_Type_RAS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_AA64PFR0_EL1_Type_RAS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_PFR0_EL1_Type_RAS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_PFR0_EL1_Type_RAS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_PFR0_Type_RAS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_AA64PFR0_EL1_Type_RME (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64PFR0_EL1_Type_RME (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _get_ID_AA64PFR0_EL1_Type_SEL2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _update_ID_AA64PFR0_EL1_Type_SEL2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_EDPFR_Type_SEL2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _get_EDPFR_Type_SEL2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_ID_AA64PFR0_EL1_Type_SVE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_ID_AA64PFR0_EL1_Type_SVE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_EDPFR_Type_SVE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_EDPFR_Type_SVE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def undefined_ICH_AP1R_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICH_AP1R_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICC_DIR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_DIR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMEVCNTSVR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMEVCNTSVR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMEVCNTSVR_EL1_Type_EVCNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_PMEVCNTSVR_EL1_Type_EVCNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def undefined_ID_AA64ISAR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64ISAR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64ISAR0_EL1_Type_AES (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_AA64ISAR0_EL1_Type_AES (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_AA64ZFR0_EL1_Type_AES (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_ISAR5_EL1_Type_AES (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_AA64ZFR0_EL1_Type_AES (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_ISAR5_EL1_Type_AES (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_ISAR5_Type_AES (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_AA64ISAR0_EL1_Type_Atomic (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_AA64ISAR0_EL1_Type_Atomic (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_AA64ISAR0_EL1_Type_CRC32 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64ISAR0_EL1_Type_CRC32 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_ISAR5_EL1_Type_CRC32 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_ISAR5_EL1_Type_CRC32 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_ISAR5_Type_CRC32 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_AA64ISAR0_EL1_Type_FHM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _update_ID_AA64ISAR0_EL1_Type_FHM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_ID_ISAR6_EL1_Type_FHM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_ISAR6_EL1_Type_FHM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_ISAR6_Type_FHM (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_AA64ISAR0_EL1_Type_RDM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_AA64ISAR0_EL1_Type_RDM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_ISAR5_EL1_Type_RDM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_ISAR5_EL1_Type_RDM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_ISAR5_Type_RDM (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_AA64ISAR0_EL1_Type_RNDR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _update_ID_AA64ISAR0_EL1_Type_RNDR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_RNDR_Type_RNDR (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _get_RNDR_Type_RNDR (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_ID_AA64ISAR0_EL1_Type_SHA1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_AA64ISAR0_EL1_Type_SHA1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_ISAR5_EL1_Type_SHA1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_ISAR5_EL1_Type_SHA1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_ISAR5_Type_SHA1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_AA64ISAR0_EL1_Type_SHA2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_AA64ISAR0_EL1_Type_SHA2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_ISAR5_EL1_Type_SHA2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_ISAR5_EL1_Type_SHA2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_ISAR5_Type_SHA2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_AA64ISAR0_EL1_Type_SHA3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_ID_AA64ISAR0_EL1_Type_SHA3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_ID_AA64ZFR0_EL1_Type_SHA3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_ID_AA64ZFR0_EL1_Type_SHA3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_ID_AA64ISAR0_EL1_Type_SM3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _update_ID_AA64ISAR0_EL1_Type_SM3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _get_ID_AA64ISAR0_EL1_Type_SM4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _update_ID_AA64ISAR0_EL1_Type_SM4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_ID_AA64ZFR0_EL1_Type_SM4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _get_ID_AA64ZFR0_EL1_Type_SM4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_ID_AA64ISAR0_EL1_Type_TLB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _update_ID_AA64ISAR0_EL1_Type_TLB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def undefined_PMMIR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMMIR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMMIR_EL1_Type_BUS_SLOTS (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _update_PMMIR_EL1_Type_BUS_SLOTS (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_PMMIR_Type_BUS_SLOTS (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _get_PMMIR_Type_BUS_SLOTS (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_PMMIR_EL1_Type_BUS_WIDTH (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_PMMIR_EL1_Type_BUS_WIDTH (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_PMMIR_Type_BUS_WIDTH (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_PMMIR_Type_BUS_WIDTH (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_PMMIR_EL1_Type_EDGE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_PMMIR_EL1_Type_EDGE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_PMMIR_Type_EDGE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_PMMIR_Type_EDGE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_PMMIR_EL1_Type_SLOTS (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_PMMIR_EL1_Type_SLOTS (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_PMMIR_Type_SLOTS (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_PMMIR_Type_SLOTS (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_PMMIR_EL1_Type_THWIDTH (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_PMMIR_EL1_Type_THWIDTH (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_PMMIR_Type_THWIDTH (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_PMMIR_Type_THWIDTH (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def undefined_ICV_IAR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_IAR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICC_IGRPEN1_EL1_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_ICC_HSRE_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICC_IGRPEN0_EL1_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICC_MSRE_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICC_SRE_EL2_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICC_SRE_EL3_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICV_IGRPEN0_EL1_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICV_IGRPEN1_EL1_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_ICC_HSRE_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICC_IGRPEN0_EL1_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICC_IGRPEN0_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICC_IGRPEN1_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICC_MSRE_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICC_SRE_EL2_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICC_SRE_EL3_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICV_IGRPEN0_EL1_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICV_IGRPEN0_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICV_IGRPEN1_EL1_Type_Enable (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICV_IGRPEN1_Type_Enable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def undefined_ID_MMFR5_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_MMFR5_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_MMFR5_EL1_Type_ETS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_MMFR5_EL1_Type_ETS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_AA64MMFR1_EL1_Type_ETS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _get_ID_AA64MMFR1_EL1_Type_ETS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_ID_MMFR5_Type_ETS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_MMFR5_EL1_Type_nTLBPA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_MMFR5_EL1_Type_nTLBPA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_AA64MMFR1_EL1_Type_nTLBPA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_ID_MMFR5_Type_nTLBPA (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_AA64MMFR1_EL1_Type_nTLBPA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_ID_MMFR5_Type_nTLBPA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def undefined_ICC_NMIAR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_NMIAR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_DBGCLAIMSET_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DBGCLAIMSET_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_DBGCLAIMSET_EL1_Type_CLAIM (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_DBGCLAIMSET_EL1_Type_CLAIM (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_DBGCLAIMCLR_EL1_Type_CLAIM (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_DBGCLAIMCLR_EL1_Type_CLAIM (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_DBGCLAIMCLR_Type_CLAIM (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_DBGCLAIMSET_Type_CLAIM (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_ICC_SRE_EL1_Type_DFB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_ICC_MSRE_Type_DFB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICC_SRE_EL2_Type_DFB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICC_SRE_EL3_Type_DFB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_ICC_HSRE_Type_DFB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICC_MSRE_Type_DFB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICC_SRE_EL2_Type_DFB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICC_SRE_EL3_Type_DFB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICC_SRE_Type_DFB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICC_SRE_EL1_Type_DIB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_ICC_MSRE_Type_DIB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICC_SRE_EL2_Type_DIB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICC_SRE_EL3_Type_DIB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_ICC_HSRE_Type_DIB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICC_MSRE_Type_DIB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICC_SRE_EL2_Type_DIB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICC_SRE_EL3_Type_DIB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICC_SRE_Type_DIB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICC_SRE_EL1_Type_SRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_ICC_MSRE_Type_SRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICC_SRE_EL2_Type_SRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICC_SRE_EL3_Type_SRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_ICC_HSRE_Type_SRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICC_MSRE_Type_SRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICC_SRE_EL2_Type_SRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICC_SRE_EL3_Type_SRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICC_SRE_Type_SRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def undefined_ICH_AP0R_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICH_AP0R_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICC_IAR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_IAR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_ISAR4_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_ISAR4_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_ISAR4_EL1_Type_Barrier (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_ISAR4_EL1_Type_Barrier (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_ISAR4_Type_Barrier (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_ISAR4_EL1_Type_PSR_M (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_ISAR4_EL1_Type_PSR_M (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_ISAR4_Type_PSR_M (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_ISAR4_EL1_Type_SMC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_ISAR4_EL1_Type_SMC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_ISAR4_Type_SMC (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_ISAR4_EL1_Type_SWP_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_ISAR4_EL1_Type_SWP_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_ISAR4_Type_SWP_frac (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_ISAR4_EL1_Type_SynchPrim_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_ISAR4_EL1_Type_SynchPrim_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_ISAR4_Type_SynchPrim_frac (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_ISAR4_EL1_Type_Unpriv (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_ISAR4_EL1_Type_Unpriv (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_ISAR4_Type_Unpriv (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_ISAR4_EL1_Type_WithShifts (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_ISAR4_EL1_Type_WithShifts (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_ISAR4_Type_WithShifts (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_ISAR4_EL1_Type_Writeback (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_ISAR4_EL1_Type_Writeback (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_ISAR4_Type_Writeback (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def undefined_ID_ISAR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_ISAR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_ISAR1_EL1_Type_Endian (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_ISAR1_EL1_Type_Endian (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_ISAR1_Type_Endian (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_ISAR1_EL1_Type_Except (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_ISAR1_EL1_Type_Except (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_ISAR1_Type_Except (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_ISAR1_EL1_Type_Except_AR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_ISAR1_EL1_Type_Except_AR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_ISAR1_Type_Except_AR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_ISAR1_EL1_Type_Extend (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_ISAR1_EL1_Type_Extend (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_ISAR1_Type_Extend (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_ISAR1_EL1_Type_IfThen (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_ISAR1_EL1_Type_IfThen (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_ISAR1_Type_IfThen (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_ISAR1_EL1_Type_Immediate (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_ISAR1_EL1_Type_Immediate (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_ISAR1_Type_Immediate (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_ISAR1_EL1_Type_Interwork (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_ISAR1_EL1_Type_Interwork (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_ISAR1_Type_Interwork (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_ISAR1_EL1_Type_Jazelle (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_ISAR1_EL1_Type_Jazelle (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_ISAR1_Type_Jazelle (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def undefined_PMUACR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMUACR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_RMR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_RMR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMSELR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSELR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMSELR_EL0_Type_SEL (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _update_PMSELR_EL0_Type_SEL (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_ERRSELR_EL1_Type_SEL (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_ERRSELR_Type_SEL (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_PMSELR_Type_SEL (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _get_ERRSELR_EL1_Type_SEL (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_ERRSELR_Type_SEL (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_PMSELR_Type_SEL (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_ICC_CTLR_EL1_Type_A3V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_GICD_TYPER_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_GICH_VTR_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_ICC_CTLR_EL3_Type_A3V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICC_CTLR_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICC_MCTLR_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICH_VTR_EL2_Type_A3V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_ICH_VTR_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_ICV_CTLR_EL1_Type_A3V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICV_CTLR_Type_A3V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_GICD_TYPER_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_GICH_VTR_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_ICC_CTLR_EL3_Type_A3V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICC_CTLR_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICC_MCTLR_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICH_VTR_EL2_Type_A3V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_ICH_VTR_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_ICV_CTLR_EL1_Type_A3V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICV_CTLR_Type_A3V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICC_CTLR_EL1_Type_CBPR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_ICC_CTLR_EL1_Type_CBPR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICC_CTLR_Type_CBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_GICV_CTLR_Type_CBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICC_CTLR_Type_CBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICV_CTLR_EL1_Type_CBPR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICV_CTLR_Type_CBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICC_CTLR_Type_CBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_GICV_CTLR_Type_CBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICC_CTLR_Type_CBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICV_CTLR_EL1_Type_CBPR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICV_CTLR_Type_CBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICC_CTLR_EL1_Type_EOImode (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_ICC_CTLR_EL1_Type_EOImode (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GICC_CTLR_Type_EOImode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_GICV_CTLR_Type_EOImode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ICC_CTLR_Type_EOImode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICV_CTLR_EL1_Type_EOImode (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICV_CTLR_Type_EOImode (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GICC_CTLR_Type_EOImode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_GICV_CTLR_Type_EOImode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICC_CTLR_Type_EOImode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICV_CTLR_EL1_Type_EOImode (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICV_CTLR_Type_EOImode (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICC_CTLR_EL1_Type_ExtRange (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_ICC_CTLR_EL3_Type_ExtRange (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ICC_CTLR_Type_ExtRange (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ICC_MCTLR_Type_ExtRange (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ICV_CTLR_EL1_Type_ExtRange (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ICV_CTLR_Type_ExtRange (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_ICC_CTLR_EL3_Type_ExtRange (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_ICC_CTLR_Type_ExtRange (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_ICC_MCTLR_Type_ExtRange (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_ICV_CTLR_EL1_Type_ExtRange (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_ICV_CTLR_Type_ExtRange (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_ICC_CTLR_EL1_Type_IDbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)

def _update_GICD_TYPER_Type_IDbits (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 19 x)

def _update_GICH_VTR_Type_IDbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 23 x)

def _update_GICR_PROPBASER_Type_IDbits (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_GICR_VPROPBASER_Type_IDbits (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_ICC_CTLR_EL3_Type_IDbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 11 x)

def _update_ICC_CTLR_Type_IDbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 11 x)

def _update_ICC_MCTLR_Type_IDbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 11 x)

def _update_ICH_VTR_EL2_Type_IDbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 23 x)

def _update_ICH_VTR_Type_IDbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 23 x)

def _update_ICV_CTLR_EL1_Type_IDbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 11 x)

def _update_ICV_CTLR_Type_IDbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 11 x)

def _get_GICD_TYPER_Type_IDbits (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 23 19)

def _get_GICH_VTR_Type_IDbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 25 23)

def _get_GICR_PROPBASER_Type_IDbits (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_GICR_VPROPBASER_Type_IDbits (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_ICC_CTLR_EL3_Type_IDbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)

def _get_ICC_CTLR_Type_IDbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)

def _get_ICC_MCTLR_Type_IDbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)

def _get_ICH_VTR_EL2_Type_IDbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 25 23)

def _get_ICH_VTR_Type_IDbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 25 23)

def _get_ICV_CTLR_EL1_Type_IDbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)

def _get_ICV_CTLR_Type_IDbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 13 11)

def _get_ICC_CTLR_EL1_Type_PMHE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_ICC_CTLR_EL1_Type_PMHE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICC_CTLR_EL3_Type_PMHE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICC_CTLR_Type_PMHE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICC_MCTLR_Type_PMHE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_ICC_CTLR_EL3_Type_PMHE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICC_CTLR_Type_PMHE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICC_MCTLR_Type_PMHE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICC_CTLR_EL1_Type_PRIbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)

def _update_GICH_VTR_Type_PRIbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 29 x)

def _update_ICC_CTLR_EL3_Type_PRIbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 8 x)

def _update_ICC_CTLR_Type_PRIbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 8 x)

def _update_ICC_MCTLR_Type_PRIbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 8 x)

def _update_ICH_VTR_EL2_Type_PRIbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 29 x)

def _update_ICH_VTR_Type_PRIbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 29 x)

def _update_ICV_CTLR_EL1_Type_PRIbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 8 x)

def _update_ICV_CTLR_Type_PRIbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 8 x)

def _get_GICH_VTR_Type_PRIbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 31 29)

def _get_ICC_CTLR_EL3_Type_PRIbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)

def _get_ICC_CTLR_Type_PRIbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)

def _get_ICC_MCTLR_Type_PRIbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)

def _get_ICH_VTR_EL2_Type_PRIbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 31 29)

def _get_ICH_VTR_Type_PRIbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 31 29)

def _get_ICV_CTLR_EL1_Type_PRIbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)

def _get_ICV_CTLR_Type_PRIbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)

def _get_ICC_CTLR_EL1_Type_RSS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_ICC_CTLR_EL1_Type_RSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_GICD_TYPER_Type_RSS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_ICC_CTLR_EL3_Type_RSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_ICC_CTLR_Type_RSS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_ICC_MCTLR_Type_RSS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_ICV_CTLR_EL1_Type_RSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_ICV_CTLR_Type_RSS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_GICD_TYPER_Type_RSS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_ICC_CTLR_EL3_Type_RSS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_ICC_CTLR_Type_RSS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_ICC_MCTLR_Type_RSS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_ICV_CTLR_EL1_Type_RSS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_ICV_CTLR_Type_RSS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_ICC_CTLR_EL1_Type_SEIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_ICC_CTLR_EL1_Type_SEIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_GICH_VTR_Type_SEIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_GITS_TYPER_Type_SEIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_ICC_CTLR_EL3_Type_SEIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICC_CTLR_Type_SEIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICC_MCTLR_Type_SEIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICH_VTR_EL2_Type_SEIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_ICH_VTR_Type_SEIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_ICV_CTLR_EL1_Type_SEIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICV_CTLR_Type_SEIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_GICH_VTR_Type_SEIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_GITS_TYPER_Type_SEIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_ICC_CTLR_EL3_Type_SEIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICC_CTLR_Type_SEIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICC_MCTLR_Type_SEIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICH_VTR_EL2_Type_SEIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_ICH_VTR_Type_SEIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_ICV_CTLR_EL1_Type_SEIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICV_CTLR_Type_SEIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def undefined_ID_ISAR6_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_ISAR6_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_ISAR6_EL1_Type_CLRBHB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_ISAR6_EL1_Type_CLRBHB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_AA64ISAR2_EL1_Type_CLRBHB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_ISAR6_Type_CLRBHB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_AA64ISAR2_EL1_Type_CLRBHB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_ISAR6_Type_CLRBHB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def undefined_ICC_AP1R_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_AP1R_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

/-- Type quantifiers: n : Int -/
def ICC_AP1R_EL1_set (n : Int) (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_AP1R_EL1_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then
    (do
      sail_assert ((0 ≤b n) && (n <b 4)) "src/v8_base.sail:44781.45-44781.46"
      writeReg ICC_AP1R_EL1_S (vectorUpdate (← readReg ICC_AP1R_EL1_S) n r))
  else
    (do
      sail_assert ((0 ≤b n) && (n <b 4)) "src/v8_base.sail:44784.45-44784.46"
      writeReg ICC_AP1R_EL1_NS (vectorUpdate (← readReg ICC_AP1R_EL1_NS) n r))

def __set_CNTP_CTL_EL0 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTP_CTL_EL0_Type := value_name
  writeReg CNTP_CTL_EL0 (Sail.BitVec.updateSubrange (← readReg CNTP_CTL_EL0) 1 0 (BitVec.slice r 0 2))
  writeReg CNTP_CTL_EL0 (Sail.BitVec.updateSubrange (← readReg CNTP_CTL_EL0) 63 3 (BitVec.slice r 3 61))

def undefined_CNTHV_TVAL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHV_TVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICH_MISR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICH_MISR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICH_MISR_EL2_Type_EOI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_ICH_MISR_EL2_Type_EOI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICH_MISR_Type_EOI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICH_MISR_Type_EOI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_MISR_Type_EOI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_MISR_EL2_Type_LRENP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_ICH_MISR_EL2_Type_LRENP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_GICH_MISR_Type_LRENP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GICH_MISR_Type_LRENP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_MISR_Type_LRENP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_MISR_EL2_Type_NP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_ICH_MISR_EL2_Type_NP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GICH_MISR_Type_NP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_GICH_MISR_Type_NP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_MISR_Type_NP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_MISR_EL2_Type_VGrp0D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_ICH_MISR_EL2_Type_VGrp0D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_GICH_MISR_Type_VGrp0D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_GICH_MISR_Type_VGrp0D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_MISR_Type_VGrp0D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_MISR_EL2_Type_VGrp0E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_ICH_MISR_EL2_Type_VGrp0E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_GICH_MISR_Type_VGrp0E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_GICH_MISR_Type_VGrp0E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_MISR_Type_VGrp0E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_MISR_EL2_Type_VGrp1D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_ICH_MISR_EL2_Type_VGrp1D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_GICH_MISR_Type_VGrp1D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_GICH_MISR_Type_VGrp1D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_MISR_Type_VGrp1D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_MISR_EL2_Type_VGrp1E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_ICH_MISR_EL2_Type_VGrp1E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_GICH_MISR_Type_VGrp1E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_GICH_MISR_Type_VGrp1E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_MISR_Type_VGrp1E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def undefined_CSSELR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CSSELR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_CSSELR_EL1_Type_InD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_CSSELR_EL1_Type_InD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CSSELR_Type_InD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_CSSELR_Type_InD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_CSSELR_EL1_Type_Level (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 3 1)

def _update_CSSELR_EL1_Type_Level (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 1 x)

def _update_CSSELR_Type_Level (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 1 x)

def _get_CSSELR_Type_Level (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 3 1)

def _get_CSSELR_EL1_Type_TnD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_CSSELR_EL1_Type_TnD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def undefined_ICV_RPR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_RPR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICV_PMR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_PMR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICV_HPPIR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_HPPIR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICV_BPR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_BPR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ISR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ISR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ISR_EL1_Type_IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_ISR_EL1_Type_IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def undefined_ID_ISAR3_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_ISAR3_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_ISAR3_EL1_Type_SIMD (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_ISAR3_EL1_Type_SIMD (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_ISAR3_Type_SIMD (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_ISAR3_EL1_Type_SVC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_ISAR3_EL1_Type_SVC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_ISAR3_Type_SVC (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_ISAR3_EL1_Type_Saturate (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_ISAR3_EL1_Type_Saturate (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_ISAR3_Type_Saturate (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_ISAR3_EL1_Type_SynchPrim (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_ISAR3_EL1_Type_SynchPrim (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_ISAR3_Type_SynchPrim (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_ISAR3_EL1_Type_T32Copy (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_ISAR3_EL1_Type_T32Copy (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_ISAR3_Type_T32Copy (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_ISAR3_EL1_Type_T32EE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_ISAR3_EL1_Type_T32EE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_ISAR3_Type_T32EE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_ISAR3_EL1_Type_TabBranch (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_ISAR3_EL1_Type_TabBranch (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_ISAR3_Type_TabBranch (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_ISAR3_EL1_Type_TrueNOP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_ISAR3_EL1_Type_TrueNOP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_ISAR3_Type_TrueNOP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def undefined_PMCCNTSVR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMCCNTSVR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MECIDR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MECIDR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MECIDR_EL2_Type_MECIDWidthm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_MECIDR_EL2_Type_MECIDWidthm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def undefined_PMINTENSET_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMINTENSET_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SMIDR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SMIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SMIDR_EL1_Type_Affinity (v : (BitVec 64)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 11 0)

def _update_SMIDR_EL1_Type_Affinity (v : (BitVec 64)) (x : (BitVec 12)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 0 x)

def _get_SMIDR_EL1_Type_SMPS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_SMIDR_EL1_Type_SMPS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def undefined_HFGWTR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HFGWTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HFGWTR_EL2_Type_AFSR0_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_HFGWTR_EL2_Type_AFSR0_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HFGRTR_EL2_Type_AFSR0_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_HFGRTR_EL2_Type_AFSR0_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_HFGWTR_EL2_Type_AFSR1_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_HFGWTR_EL2_Type_AFSR1_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_HFGRTR_EL2_Type_AFSR1_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_HFGRTR_EL2_Type_AFSR1_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_HFGWTR_EL2_Type_AMAIR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_HFGWTR_EL2_Type_AMAIR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_HFGRTR_EL2_Type_AMAIR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_HFGRTR_EL2_Type_AMAIR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_HFGWTR_EL2_Type_APDAKey (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_HFGWTR_EL2_Type_APDAKey (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_HFGRTR_EL2_Type_APDAKey (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_HFGRTR_EL2_Type_APDAKey (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_HFGWTR_EL2_Type_APDBKey (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_HFGWTR_EL2_Type_APDBKey (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_HFGRTR_EL2_Type_APDBKey (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_HFGRTR_EL2_Type_APDBKey (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_HFGWTR_EL2_Type_APGAKey (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_HFGWTR_EL2_Type_APGAKey (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_HFGRTR_EL2_Type_APGAKey (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_HFGRTR_EL2_Type_APGAKey (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_HFGWTR_EL2_Type_APIAKey (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_HFGWTR_EL2_Type_APIAKey (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HFGRTR_EL2_Type_APIAKey (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_HFGRTR_EL2_Type_APIAKey (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_HFGWTR_EL2_Type_APIBKey (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_HFGWTR_EL2_Type_APIBKey (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_HFGRTR_EL2_Type_APIBKey (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_HFGRTR_EL2_Type_APIBKey (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_HFGWTR_EL2_Type_CONTEXTIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_HFGWTR_EL2_Type_CONTEXTIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_HFGRTR_EL2_Type_CONTEXTIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMVCIDSR_Type_CONTEXTIDR_EL1 (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_HFGRTR_EL2_Type_CONTEXTIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMVCIDSR_Type_CONTEXTIDR_EL1 (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_HFGWTR_EL2_Type_CPACR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_HFGWTR_EL2_Type_CPACR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_HFGRTR_EL2_Type_CPACR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_HFGRTR_EL2_Type_CPACR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_HFGWTR_EL2_Type_CSSELR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_HFGWTR_EL2_Type_CSSELR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_HFGRTR_EL2_Type_CSSELR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_HFGRTR_EL2_Type_CSSELR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_HFGWTR_EL2_Type_ERRSELR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _update_HFGWTR_EL2_Type_ERRSELR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_HFGRTR_EL2_Type_ERRSELR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _get_HFGRTR_EL2_Type_ERRSELR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _get_HFGWTR_EL2_Type_ERXADDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _update_HFGWTR_EL2_Type_ERXADDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _update_HFGRTR_EL2_Type_ERXADDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _get_HFGRTR_EL2_Type_ERXADDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _get_HFGWTR_EL2_Type_ERXCTLR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _update_HFGWTR_EL2_Type_ERXCTLR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_HFGRTR_EL2_Type_ERXCTLR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _get_HFGRTR_EL2_Type_ERXCTLR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _get_HFGWTR_EL2_Type_ERXMISCn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _update_HFGWTR_EL2_Type_ERXMISCn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_HFGRTR_EL2_Type_ERXMISCn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _get_HFGRTR_EL2_Type_ERXMISCn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _get_HFGWTR_EL2_Type_ERXPFGCDN_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_HFGWTR_EL2_Type_ERXPFGCDN_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_HFGRTR_EL2_Type_ERXPFGCDN_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _get_HFGRTR_EL2_Type_ERXPFGCDN_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _get_HFGWTR_EL2_Type_ERXPFGCTL_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _update_HFGWTR_EL2_Type_ERXPFGCTL_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _update_HFGRTR_EL2_Type_ERXPFGCTL_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _get_HFGRTR_EL2_Type_ERXPFGCTL_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _get_HFGWTR_EL2_Type_ERXSTATUS_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _update_HFGWTR_EL2_Type_ERXSTATUS_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_HFGRTR_EL2_Type_ERXSTATUS_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _get_HFGRTR_EL2_Type_ERXSTATUS_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _get_HFGWTR_EL2_Type_ESR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_HFGWTR_EL2_Type_ESR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_HFGRTR_EL2_Type_ESR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_HFGRTR_EL2_Type_ESR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_HFGWTR_EL2_Type_FAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_HFGWTR_EL2_Type_FAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_HFGRTR_EL2_Type_FAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_HFGRTR_EL2_Type_FAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_HFGWTR_EL2_Type_ICC_IGRPENn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _update_HFGWTR_EL2_Type_ICC_IGRPENn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _update_HFGRTR_EL2_Type_ICC_IGRPENn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _get_HFGRTR_EL2_Type_ICC_IGRPENn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _get_HFGWTR_EL2_Type_LORC_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_HFGWTR_EL2_Type_LORC_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_HFGRTR_EL2_Type_LORC_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_HFGRTR_EL2_Type_LORC_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_HFGWTR_EL2_Type_LOREA_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_HFGWTR_EL2_Type_LOREA_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_HFGRTR_EL2_Type_LOREA_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_HFGRTR_EL2_Type_LOREA_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_HFGWTR_EL2_Type_LORN_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_HFGWTR_EL2_Type_LORN_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_HFGRTR_EL2_Type_LORN_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_HFGRTR_EL2_Type_LORN_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_HFGWTR_EL2_Type_LORSA_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_HFGWTR_EL2_Type_LORSA_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_HFGRTR_EL2_Type_LORSA_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_HFGRTR_EL2_Type_LORSA_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_HFGWTR_EL2_Type_MAIR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_HFGWTR_EL2_Type_MAIR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_HFGRTR_EL2_Type_MAIR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_HFGRTR_EL2_Type_MAIR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_HFGWTR_EL2_Type_PAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_HFGWTR_EL2_Type_PAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_HFGRTR_EL2_Type_PAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_HFGRTR_EL2_Type_PAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_HFGWTR_EL2_Type_SCTLR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_HFGWTR_EL2_Type_SCTLR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_HFGRTR_EL2_Type_SCTLR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_HFGRTR_EL2_Type_SCTLR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_HFGWTR_EL2_Type_SCXTNUM_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_HFGWTR_EL2_Type_SCXTNUM_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_HFGRTR_EL2_Type_SCXTNUM_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_HFGRTR_EL2_Type_SCXTNUM_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_HFGWTR_EL2_Type_SCXTNUM_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_HFGWTR_EL2_Type_SCXTNUM_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_HFGRTR_EL2_Type_SCXTNUM_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_HFGRTR_EL2_Type_SCXTNUM_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_HFGWTR_EL2_Type_TCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_HFGWTR_EL2_Type_TCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_HFGRTR_EL2_Type_TCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _get_HFGRTR_EL2_Type_TCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_HFGWTR_EL2_Type_TPIDRRO_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _update_HFGWTR_EL2_Type_TPIDRRO_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_HFGRTR_EL2_Type_TPIDRRO_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _get_HFGRTR_EL2_Type_TPIDRRO_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _get_HFGWTR_EL2_Type_TPIDR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _update_HFGWTR_EL2_Type_TPIDR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_HFGRTR_EL2_Type_TPIDR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _get_HFGRTR_EL2_Type_TPIDR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _get_HFGWTR_EL2_Type_TPIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_HFGWTR_EL2_Type_TPIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_HFGRTR_EL2_Type_TPIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _get_HFGRTR_EL2_Type_TPIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _get_HFGWTR_EL2_Type_TTBR0_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_HFGWTR_EL2_Type_TTBR0_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_HFGRTR_EL2_Type_TTBR0_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _get_HFGRTR_EL2_Type_TTBR0_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _get_HFGWTR_EL2_Type_TTBR1_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_HFGWTR_EL2_Type_TTBR1_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_HFGRTR_EL2_Type_TTBR1_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _get_HFGRTR_EL2_Type_TTBR1_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _get_HFGWTR_EL2_Type_VBAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)

def _update_HFGWTR_EL2_Type_VBAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_HFGRTR_EL2_Type_VBAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _get_HFGRTR_EL2_Type_VBAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)

def _get_HFGWTR_EL2_Type_nACCDATA_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _update_HFGWTR_EL2_Type_nACCDATA_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_HFGRTR_EL2_Type_nACCDATA_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _get_HFGRTR_EL2_Type_nACCDATA_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _get_HFGWTR_EL2_Type_nAMAIR2_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_HFGWTR_EL2_Type_nAMAIR2_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_HFGRTR_EL2_Type_nAMAIR2_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _get_HFGRTR_EL2_Type_nAMAIR2_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_HFGWTR_EL2_Type_nGCS_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _update_HFGWTR_EL2_Type_nGCS_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_HFGRTR_EL2_Type_nGCS_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _get_HFGRTR_EL2_Type_nGCS_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _get_HFGWTR_EL2_Type_nGCS_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _update_HFGWTR_EL2_Type_nGCS_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_HFGRTR_EL2_Type_nGCS_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _get_HFGRTR_EL2_Type_nGCS_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _get_HFGWTR_EL2_Type_nMAIR2_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_HFGWTR_EL2_Type_nMAIR2_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_HFGRTR_EL2_Type_nMAIR2_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _get_HFGRTR_EL2_Type_nMAIR2_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_HFGWTR_EL2_Type_nPIRE0_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _update_HFGWTR_EL2_Type_nPIRE0_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_HFGRTR_EL2_Type_nPIRE0_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _get_HFGRTR_EL2_Type_nPIRE0_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _get_HFGWTR_EL2_Type_nPIR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_HFGWTR_EL2_Type_nPIR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_HFGRTR_EL2_Type_nPIR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _get_HFGRTR_EL2_Type_nPIR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _get_HFGWTR_EL2_Type_nPOR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_HFGWTR_EL2_Type_nPOR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_HFGRTR_EL2_Type_nPOR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _get_HFGRTR_EL2_Type_nPOR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _get_HFGWTR_EL2_Type_nPOR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_HFGWTR_EL2_Type_nPOR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_HFGRTR_EL2_Type_nPOR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _get_HFGRTR_EL2_Type_nPOR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _get_HFGWTR_EL2_Type_nRCWMASK_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _update_HFGWTR_EL2_Type_nRCWMASK_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _update_HFGRTR_EL2_Type_nRCWMASK_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _get_HFGRTR_EL2_Type_nRCWMASK_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _get_HFGWTR_EL2_Type_nS2POR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _update_HFGWTR_EL2_Type_nS2POR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_HFGRTR_EL2_Type_nS2POR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _get_HFGRTR_EL2_Type_nS2POR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_HFGWTR_EL2_Type_nSMPRI_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _update_HFGWTR_EL2_Type_nSMPRI_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_HFGRTR_EL2_Type_nSMPRI_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _get_HFGRTR_EL2_Type_nSMPRI_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _get_HFGWTR_EL2_Type_nTPIDR2_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _update_HFGWTR_EL2_Type_nTPIDR2_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_HFGRTR_EL2_Type_nTPIDR2_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _get_HFGRTR_EL2_Type_nTPIDR2_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def undefined_SMPRI_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SMPRI_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMUSERENR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMUSERENR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMUSERENR_EL0_Type_CR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_PMUSERENR_EL0_Type_CR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMUSERENR_Type_CR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_PMUSERENR_Type_CR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMUSERENR_EL0_Type_ER (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_PMUSERENR_EL0_Type_ER (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMUSERENR_Type_ER (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_PMUSERENR_Type_ER (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMUSERENR_EL0_Type_IR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_PMUSERENR_EL0_Type_IR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_GICR_CTLR_Type_IR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GICR_CTLR_Type_IR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMUSERENR_EL0_Type_TID (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_PMUSERENR_EL0_Type_TID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMUSERENR_Type_TID (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_PMUSERENR_Type_TID (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMUSERENR_EL0_Type_UEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_PMUSERENR_EL0_Type_UEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCFGR_Type_UEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_PMCFGR_Type_UEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def undefined_ICV_CTLR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_CTLR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICV_IAR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_IAR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def __set_MDSCR_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MDSCR_EL1_Type := value_name
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 5 0 (BitVec.slice r 0 6))
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 13 7 (BitVec.slice r 7 7))
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 18 15 (BitVec.slice r 15 4))
  writeReg MDSCR_EL1 (BitVec.update (← readReg MDSCR_EL1) 20 (Bit (BitVec.slice r 20 1)))
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 25 24 (BitVec.slice r 24 2))
  writeReg MDSCR_EL1 (BitVec.update (← readReg MDSCR_EL1) 28 (Bit (BitVec.slice r 28 1)))
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 34 32 (BitVec.slice r 32 3))
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 63 36 (BitVec.slice r 36 28))
  if ((! ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 0#1)) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 35 35 (_get_MDSCR_EL1_Type_EHBWE r))
  else (pure ())
  if (((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 31 31 (_get_MDSCR_EL1_Type_TFO r))
  else (pure ())
  if (((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 30 30 (_get_MDSCR_EL1_Type_RXfull r))
  else (pure ())
  if (((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 29 29 (_get_MDSCR_EL1_Type_TXfull r))
  else (pure ())
  if (((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 27 27 (_get_MDSCR_EL1_Type_RXO r))
  else (pure ())
  if (((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 26 26 (_get_MDSCR_EL1_Type_TXU r))
  else (pure ())
  if (((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 23 22 (_get_MDSCR_EL1_Type_INTdis r))
  else (pure ())
  if (((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 21 21 (_get_MDSCR_EL1_Type_TDA r))
  else (pure ())
  if (((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 19 19 (_get_MDSCR_EL1_Type_SC2 r))
  else (pure ())
  if (((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 14 14 (_get_MDSCR_EL1_Type_HDE r))
  else (pure ())
  if (((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1) : Bool)
  then writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 6 6 (_get_MDSCR_EL1_Type_ERR r))
  else (pure ())

def __set_GPCCR_EL3 (value_name : (BitVec 64)) : SailM Unit := do
  let r : GPCCR_EL3_Type := value_name
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange (← readReg GPCCR_EL3) 19 0 (BitVec.slice r 0 20))
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange (← readReg GPCCR_EL3) 63 24 (BitVec.slice r 24 40))

def undefined_ID_PFR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_PFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_PFR0_EL1_Type_State0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_PFR0_EL1_Type_State0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_PFR0_Type_State0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_PFR0_EL1_Type_State1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_PFR0_EL1_Type_State1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_PFR0_Type_State1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_PFR0_EL1_Type_State2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_PFR0_EL1_Type_State2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_PFR0_Type_State2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_PFR0_EL1_Type_State3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_PFR0_EL1_Type_State3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_PFR0_Type_State3 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def undefined_MVFR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MVFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MVFR1_EL1_Type_FPDNaN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_MVFR1_EL1_Type_FPDNaN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_MVFR1_Type_FPDNaN (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_MVFR1_EL1_Type_FPFtZ (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_MVFR1_EL1_Type_FPFtZ (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_MVFR1_Type_FPFtZ (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_MVFR1_EL1_Type_FPHP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_MVFR1_EL1_Type_FPHP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_MVFR1_Type_FPHP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_MVFR1_EL1_Type_SIMDFMAC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_MVFR1_EL1_Type_SIMDFMAC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_MVFR1_Type_SIMDFMAC (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_MVFR1_EL1_Type_SIMDHP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_MVFR1_EL1_Type_SIMDHP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_MVFR1_Type_SIMDHP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_MVFR1_EL1_Type_SIMDInt (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_MVFR1_EL1_Type_SIMDInt (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_MVFR1_Type_SIMDInt (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_MVFR1_EL1_Type_SIMDLS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_MVFR1_EL1_Type_SIMDLS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_MVFR1_Type_SIMDLS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_MVFR1_EL1_Type_SIMDSP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_MVFR1_EL1_Type_SIMDSP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_MVFR1_Type_SIMDSP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def undefined_HDFGWTR2_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HDFGWTR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HDFGWTR2_EL2_Type_nMDSELR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_HDFGWTR2_EL2_Type_nMDSELR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_HDFGRTR2_EL2_Type_nMDSELR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_HDFGRTR2_EL2_Type_nMDSELR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_HDFGWTR2_EL2_Type_nPMECR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_HDFGWTR2_EL2_Type_nPMECR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HDFGRTR2_EL2_Type_nPMECR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_HDFGRTR2_EL2_Type_nPMECR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_HDFGWTR2_EL2_Type_nPMIAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_HDFGWTR2_EL2_Type_nPMIAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_HDFGRTR2_EL2_Type_nPMIAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_HDFGRTR2_EL2_Type_nPMIAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_HDFGWTR2_EL2_Type_nPMICFILTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_HDFGWTR2_EL2_Type_nPMICFILTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_HDFGRTR2_EL2_Type_nPMICFILTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_HDFGRTR2_EL2_Type_nPMICFILTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_HDFGWTR2_EL2_Type_nPMICNTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_HDFGWTR2_EL2_Type_nPMICNTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_HDFGRTR2_EL2_Type_nPMICNTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_HDFGRTR2_EL2_Type_nPMICNTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_HDFGWTR2_EL2_Type_nPMSDSFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_HDFGWTR2_EL2_Type_nPMSDSFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_HDFGRTR2_EL2_Type_nPMSDSFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_HDFGRTR2_EL2_Type_nPMSDSFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_HDFGWTR2_EL2_Type_nPMSSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_HDFGWTR2_EL2_Type_nPMSSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HDFGRTR2_EL2_Type_nPMSSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_HDFGRTR2_EL2_Type_nPMSSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_HDFGWTR2_EL2_Type_nPMUACR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_HDFGWTR2_EL2_Type_nPMUACR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_HDFGRTR2_EL2_Type_nPMUACR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_HDFGRTR2_EL2_Type_nPMUACR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_HDFGWTR2_EL2_Type_nPMZR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_HDFGWTR2_EL2_Type_nPMZR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_HDFGWTR2_EL2_Type_nSPMACCESSR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_HDFGWTR2_EL2_Type_nSPMACCESSR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_HDFGRTR2_EL2_Type_nSPMACCESSR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_HDFGRTR2_EL2_Type_nSPMACCESSR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_HDFGWTR2_EL2_Type_nSPMCNTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_HDFGWTR2_EL2_Type_nSPMCNTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_HDFGRTR2_EL2_Type_nSPMCNTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_HDFGRTR2_EL2_Type_nSPMCNTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_HDFGWTR2_EL2_Type_nSPMCR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_HDFGWTR2_EL2_Type_nSPMCR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_HDFGRTR2_EL2_Type_nSPMCR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_HDFGRTR2_EL2_Type_nSPMCR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_HDFGWTR2_EL2_Type_nSPMINTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_HDFGWTR2_EL2_Type_nSPMINTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_HDFGRTR2_EL2_Type_nSPMINTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_HDFGRTR2_EL2_Type_nSPMINTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_HDFGWTR2_EL2_Type_nSPMOVS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_HDFGWTR2_EL2_Type_nSPMOVS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_HDFGRTR2_EL2_Type_nSPMOVS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_HDFGRTR2_EL2_Type_nSPMOVS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_HDFGWTR2_EL2_Type_nSPMSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_HDFGWTR2_EL2_Type_nSPMSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_HDFGRTR2_EL2_Type_nSPMSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_HDFGRTR2_EL2_Type_nSPMSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_HDFGWTR2_EL2_Type_nSPMSELR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_HDFGWTR2_EL2_Type_nSPMSELR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_HDFGRTR2_EL2_Type_nSPMSELR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_HDFGRTR2_EL2_Type_nSPMSELR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def undefined_ID_ISAR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_ISAR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_ISAR0_EL1_Type_BitCount (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_ISAR0_EL1_Type_BitCount (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_ISAR0_Type_BitCount (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_ISAR0_EL1_Type_BitField (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_ISAR0_EL1_Type_BitField (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_ISAR0_Type_BitField (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_ISAR0_EL1_Type_CmpBranch (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_ISAR0_EL1_Type_CmpBranch (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_ISAR0_Type_CmpBranch (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_ISAR0_EL1_Type_Coproc (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_ISAR0_EL1_Type_Coproc (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_ISAR0_Type_Coproc (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_ISAR0_EL1_Type_Debug (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_ISAR0_EL1_Type_Debug (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_ISAR0_Type_Debug (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_ISAR0_EL1_Type_Divide (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_ISAR0_EL1_Type_Divide (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_ISAR0_Type_Divide (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_ISAR0_EL1_Type_Swap (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_ISAR0_EL1_Type_Swap (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_ISAR0_Type_Swap (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def __set_CNTHP_CTL_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTHP_CTL_EL2_Type := value_name
  writeReg CNTHP_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHP_CTL_EL2) 1 0 (BitVec.slice r 0 2))
  writeReg CNTHP_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHP_CTL_EL2) 63 3 (BitVec.slice r 3 61))

def undefined_CNTHVS_TVAL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHVS_TVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTHP_TVAL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHP_TVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SPMACCESSR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPMACCESSR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMZR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMZR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMICNTSVR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMICNTSVR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MDRAR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MDRAR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MDRAR_EL1_Type_ROMADDR (v : (BitVec 64)) : (BitVec 44) :=
  (Sail.BitVec.extractLsb v 55 12)

def _update_MDRAR_EL1_Type_ROMADDR (v : (BitVec 64)) (x : (BitVec 44)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 12 x)

def _update_DBGDRAR_Type_ROMADDR (v : (BitVec 64)) (x : (BitVec 36)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 12 x)

def _get_DBGDRAR_Type_ROMADDR (v : (BitVec 64)) : (BitVec 36) :=
  (Sail.BitVec.extractLsb v 47 12)

def _get_MDRAR_EL1_Type_Valid (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_MDRAR_EL1_Type_Valid (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_DBGDRAR_Type_Valid (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_GICM_TYPER_Type_Valid (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_GICR_VPENDBASER_Type_Valid (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_GICR_VPROPBASER_Type_Valid (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_GITS_CBASER_Type_Valid (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_LORSA_EL1_Type_Valid (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_DBGDRAR_Type_Valid (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _get_GICM_TYPER_Type_Valid (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_GICR_VPENDBASER_Type_Valid (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_GICR_VPROPBASER_Type_Valid (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_GITS_CBASER_Type_Valid (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_LORSA_EL1_Type_Valid (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def undefined_ICC_IGRPEN1_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_IGRPEN1_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICC_IGRPEN1_EL3_Type_EnableGrp1NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_ICC_IGRPEN1_EL3_Type_EnableGrp1NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICD_CTLR_Type_EnableGrp1NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICC_MGRPEN1_Type_EnableGrp1NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICD_CTLR_Type_EnableGrp1NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICC_MGRPEN1_Type_EnableGrp1NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICC_IGRPEN1_EL3_Type_EnableGrp1S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_ICC_IGRPEN1_EL3_Type_EnableGrp1S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GICD_CTLR_Type_EnableGrp1S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICC_MGRPEN1_Type_EnableGrp1S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GICD_CTLR_Type_EnableGrp1S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICC_MGRPEN1_Type_EnableGrp1S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def undefined_ID_MMFR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_MMFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_MMFR1_EL1_Type_BPred (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_MMFR1_EL1_Type_BPred (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_MMFR1_Type_BPred (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_MMFR1_EL1_Type_L1Hvd (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_MMFR1_EL1_Type_L1Hvd (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_MMFR1_Type_L1Hvd (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_MMFR1_EL1_Type_L1HvdSW (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_MMFR1_EL1_Type_L1HvdSW (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_MMFR1_Type_L1HvdSW (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_MMFR1_EL1_Type_L1HvdVA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_MMFR1_EL1_Type_L1HvdVA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_MMFR1_Type_L1HvdVA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_MMFR1_EL1_Type_L1TstCln (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_MMFR1_EL1_Type_L1TstCln (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_MMFR1_Type_L1TstCln (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_MMFR1_EL1_Type_L1Uni (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_MMFR1_EL1_Type_L1Uni (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_MMFR1_Type_L1Uni (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_MMFR1_EL1_Type_L1UniSW (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_MMFR1_EL1_Type_L1UniSW (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_MMFR1_Type_L1UniSW (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_MMFR1_EL1_Type_L1UniVA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_MMFR1_EL1_Type_L1UniVA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_MMFR1_Type_L1UniVA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def undefined_LORSA_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_LORSA_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_AA64MMFR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64MMFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64MMFR1_EL1_Type_AFP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _update_ID_AA64MMFR1_EL1_Type_AFP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _get_ID_AA64MMFR1_EL1_Type_ECBHB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _update_ID_AA64MMFR1_EL1_Type_ECBHB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _get_ID_AA64MMFR1_EL1_Type_HAFDBS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_AA64MMFR1_EL1_Type_HAFDBS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_AA64MMFR1_EL1_Type_HCX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _update_ID_AA64MMFR1_EL1_Type_HCX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _get_ID_AA64MMFR1_EL1_Type_LO (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64MMFR1_EL1_Type_LO (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_AA64MMFR1_EL1_Type_TIDCP1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64MMFR1_EL1_Type_TIDCP1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _get_ID_AA64MMFR1_EL1_Type_TWED (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_ID_AA64MMFR1_EL1_Type_TWED (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_ID_AA64MMFR1_EL1_Type_VH (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_AA64MMFR1_EL1_Type_VH (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_AA64MMFR1_EL1_Type_VMIDBits (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_AA64MMFR1_EL1_Type_VMIDBits (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def undefined_PMSWINC_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSWINC_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def __set_CNTV_CTL_EL0 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTV_CTL_EL0_Type := value_name
  writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange (← readReg CNTV_CTL_EL0) 1 0 (BitVec.slice r 0 2))
  writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange (← readReg CNTV_CTL_EL0) 63 3 (BitVec.slice r 3 61))

def undefined_PMIAR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMIAR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_MMFR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_MMFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_MMFR0_EL1_Type_AuxReg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_MMFR0_EL1_Type_AuxReg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_MMFR0_Type_AuxReg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_MMFR0_EL1_Type_FCSE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_MMFR0_EL1_Type_FCSE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_MMFR0_Type_FCSE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_MMFR0_EL1_Type_InnerShr (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_MMFR0_EL1_Type_InnerShr (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_MMFR0_Type_InnerShr (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_MMFR0_EL1_Type_OuterShr (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_MMFR0_EL1_Type_OuterShr (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_MMFR0_Type_OuterShr (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_MMFR0_EL1_Type_PMSA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_MMFR0_EL1_Type_PMSA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_EDAA32PFR_Type_PMSA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_EDAA32PFR_Type_PMSA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_MMFR0_Type_PMSA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_MMFR0_EL1_Type_ShareLvl (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_MMFR0_EL1_Type_ShareLvl (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_MMFR0_Type_ShareLvl (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_MMFR0_EL1_Type_TCM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_MMFR0_EL1_Type_TCM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_MMFR0_Type_TCM (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_MMFR0_EL1_Type_VMSA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_MMFR0_EL1_Type_VMSA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_EDAA32PFR_Type_VMSA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_EDAA32PFR_Type_VMSA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_MMFR0_Type_VMSA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def undefined_ICH_VMCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICH_VMCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICH_VMCR_EL2_Type_VAckCtl (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_ICH_VMCR_EL2_Type_VAckCtl (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_GICH_VMCR_Type_VAckCtl (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICH_VMCR_Type_VAckCtl (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GICH_VMCR_Type_VAckCtl (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_VMCR_Type_VAckCtl (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_VMCR_EL2_Type_VBPR0 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 23 21)

def _update_ICH_VMCR_EL2_Type_VBPR0 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 21 x)

def _update_GICH_VMCR_Type_VBPR0 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 21 x)

def _update_ICH_VMCR_Type_VBPR0 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 21 x)

def _get_GICH_VMCR_Type_VBPR0 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 23 21)

def _get_ICH_VMCR_Type_VBPR0 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 23 21)

def _get_ICH_VMCR_EL2_Type_VBPR1 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)

def _update_ICH_VMCR_EL2_Type_VBPR1 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 18 x)

def _update_GICH_VMCR_Type_VBPR1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 18 x)

def _update_ICH_VMCR_Type_VBPR1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 18 x)

def _get_GICH_VMCR_Type_VBPR1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)

def _get_ICH_VMCR_Type_VBPR1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)

def _get_ICH_VMCR_EL2_Type_VCBPR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_ICH_VMCR_EL2_Type_VCBPR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_GICH_VMCR_Type_VCBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICH_VMCR_Type_VCBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_GICH_VMCR_Type_VCBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_VMCR_Type_VCBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_VMCR_EL2_Type_VENG0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_ICH_VMCR_EL2_Type_VENG0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICH_VMCR_Type_VENG0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_VMCR_Type_VENG0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICH_VMCR_Type_VENG0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_VMCR_Type_VENG0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_VMCR_EL2_Type_VENG1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_ICH_VMCR_EL2_Type_VENG1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GICH_VMCR_Type_VENG1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_VMCR_Type_VENG1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GICH_VMCR_Type_VENG1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_VMCR_Type_VENG1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_VMCR_EL2_Type_VEOIM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_ICH_VMCR_EL2_Type_VEOIM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_GICH_VMCR_Type_VEOIM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ICH_VMCR_Type_VEOIM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_GICH_VMCR_Type_VEOIM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICH_VMCR_Type_VEOIM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICH_VMCR_EL2_Type_VFIQEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_ICH_VMCR_EL2_Type_VFIQEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GICH_VMCR_Type_VFIQEn (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICH_VMCR_Type_VFIQEn (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_GICH_VMCR_Type_VFIQEn (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_VMCR_Type_VFIQEn (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_VMCR_EL2_Type_VPMR (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _update_ICH_VMCR_EL2_Type_VPMR (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_GICH_VMCR_Type_VPMR (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_ICH_VMCR_Type_VPMR (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _get_GICH_VMCR_Type_VPMR (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_ICH_VMCR_Type_VPMR (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def undefined_VPIDR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VPIDR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICC_CTLR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_CTLR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICC_CTLR_EL3_Type_CBPR_EL1NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_ICC_CTLR_EL3_Type_CBPR_EL1NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICC_MCTLR_Type_CBPR_EL1NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_ICC_MCTLR_Type_CBPR_EL1NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICC_CTLR_EL3_Type_CBPR_EL1S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_ICC_CTLR_EL3_Type_CBPR_EL1S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICC_MCTLR_Type_CBPR_EL1S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_ICC_MCTLR_Type_CBPR_EL1S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICC_CTLR_EL3_Type_EOImode_EL1NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_ICC_CTLR_EL3_Type_EOImode_EL1NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICC_MCTLR_Type_EOImode_EL1NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_ICC_MCTLR_Type_EOImode_EL1NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICC_CTLR_EL3_Type_EOImode_EL1S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_ICC_CTLR_EL3_Type_EOImode_EL1S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICC_MCTLR_Type_EOImode_EL1S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_ICC_MCTLR_Type_EOImode_EL1S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICC_CTLR_EL3_Type_EOImode_EL3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_ICC_CTLR_EL3_Type_EOImode_EL3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICC_MCTLR_Type_EOImode_EL3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_ICC_MCTLR_Type_EOImode_EL3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICC_CTLR_EL3_Type_RM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_ICC_CTLR_EL3_Type_RM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ICC_MCTLR_Type_RM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_ICC_MCTLR_Type_RM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICC_CTLR_EL3_Type_nDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_ICC_CTLR_EL3_Type_nDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_ICC_MCTLR_Type_nDS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_ICC_MCTLR_Type_nDS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def undefined_ICC_SRE_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_SRE_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def __set_CNTPS_CTL_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTPS_CTL_EL1_Type := value_name
  writeReg CNTPS_CTL_EL1 (Sail.BitVec.updateSubrange (← readReg CNTPS_CTL_EL1) 1 0 (BitVec.slice r 0 2))
  writeReg CNTPS_CTL_EL1 (Sail.BitVec.updateSubrange (← readReg CNTPS_CTL_EL1) 63 3 (BitVec.slice r 3 61))

def undefined_LORC_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_LORC_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_AA64PFR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64PFR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64PFR2_EL1_Type_MTEFAR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_AA64PFR2_EL1_Type_MTEFAR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_AA64PFR2_EL1_Type_MTEPERM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_AA64PFR2_EL1_Type_MTEPERM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_AA64PFR2_EL1_Type_MTESTOREONLY (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_AA64PFR2_EL1_Type_MTESTOREONLY (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def undefined_CCSIDR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CCSIDR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_CCSIDR2_EL1_Type_NumSets (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _update_CCSIDR2_EL1_Type_NumSets (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_CCSIDR2_Type_NumSets (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_CCSIDR_Type_NumSets (v : (BitVec 32)) (x : (BitVec 15)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 13 x)

def _get_CCSIDR2_Type_NumSets (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_CCSIDR_Type_NumSets (v : (BitVec 32)) : (BitVec 15) :=
  (Sail.BitVec.extractLsb v 27 13)

def undefined_ICC_ASGI1R_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_ASGI1R_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_AA64ISAR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64ISAR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64ISAR2_EL1_Type_APA3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_AA64ISAR2_EL1_Type_APA3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_AA64ISAR2_EL1_Type_BC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_AA64ISAR2_EL1_Type_BC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_AA64ISAR2_EL1_Type_CSSC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64ISAR2_EL1_Type_CSSC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _get_ID_AA64ISAR2_EL1_Type_GPA3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_AA64ISAR2_EL1_Type_GPA3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_AA64ISAR2_EL1_Type_MOPS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64ISAR2_EL1_Type_MOPS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_AA64ISAR2_EL1_Type_PAC_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_AA64ISAR2_EL1_Type_PAC_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_AA64ISAR2_EL1_Type_PRFMSLC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _update_ID_AA64ISAR2_EL1_Type_PRFMSLC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _get_ID_AA64ISAR2_EL1_Type_RPRES (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_AA64ISAR2_EL1_Type_RPRES (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_AA64ISAR2_EL1_Type_RPRFM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _update_ID_AA64ISAR2_EL1_Type_RPRFM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _get_ID_AA64ISAR2_EL1_Type_SYSINSTR_128 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _update_ID_AA64ISAR2_EL1_Type_SYSINSTR_128 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _get_ID_AA64ISAR2_EL1_Type_SYSREG_128 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_ID_AA64ISAR2_EL1_Type_SYSREG_128 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_ID_AA64ISAR2_EL1_Type_WFxT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_AA64ISAR2_EL1_Type_WFxT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def undefined_HFGRTR2_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HFGRTR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HFGRTR2_EL2_Type_nERXGSR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_HFGRTR2_EL2_Type_nERXGSR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_HFGRTR2_EL2_Type_nPFAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_HFGRTR2_EL2_Type_nPFAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HFGWTR2_EL2_Type_nPFAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_HFGWTR2_EL2_Type_nPFAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_HFGRTR2_EL2_Type_nRCWSMASK_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_HFGRTR2_EL2_Type_nRCWSMASK_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_HFGWTR2_EL2_Type_nRCWSMASK_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_HFGWTR2_EL2_Type_nRCWSMASK_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def undefined_ID_ISAR5_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_ISAR5_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_ISAR5_EL1_Type_SEVL (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_ISAR5_EL1_Type_SEVL (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_ISAR5_Type_SEVL (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_ISAR5_EL1_Type_VCMA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_ISAR5_EL1_Type_VCMA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_ISAR5_Type_VCMA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def undefined_RMR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_RMR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICH_HCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICH_HCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICH_HCR_EL2_Type_DVIM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_ICH_HCR_EL2_Type_DVIM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICH_VTR_EL2_Type_DVIM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_ICH_VTR_EL2_Type_DVIM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_ICH_HCR_EL2_Type_EOIcount (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 31 27)

def _update_ICH_HCR_EL2_Type_EOIcount (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 27 x)

def _get_ICH_HCR_Type_EOIcount (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 31 27)

def _get_ICH_HCR_EL2_Type_En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_ICH_HCR_EL2_Type_En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICH_HCR_Type_En (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICH_HCR_Type_En (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_HCR_Type_En (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_HCR_EL2_Type_LRENPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_ICH_HCR_EL2_Type_LRENPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_GICH_HCR_Type_LRENPIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GICH_HCR_Type_LRENPIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_HCR_Type_LRENPIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_HCR_EL2_Type_NPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_ICH_HCR_EL2_Type_NPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GICH_HCR_Type_NPIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_GICH_HCR_Type_NPIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_HCR_Type_NPIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_HCR_EL2_Type_TALL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_ICH_HCR_EL2_Type_TALL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_ICH_HCR_Type_TALL0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_ICH_HCR_EL2_Type_TALL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_ICH_HCR_EL2_Type_TALL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_ICH_HCR_Type_TALL1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_ICH_HCR_EL2_Type_TDIR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_ICH_HCR_EL2_Type_TDIR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_ICH_HCR_Type_TDIR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICH_HCR_EL2_Type_TSEI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_ICH_HCR_EL2_Type_TSEI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_ICH_HCR_Type_TSEI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_ICH_HCR_EL2_Type_UIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_ICH_HCR_EL2_Type_UIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GICH_HCR_Type_UIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GICH_HCR_Type_UIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_HCR_Type_UIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_HCR_EL2_Type_VGrp0DIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_ICH_HCR_EL2_Type_VGrp0DIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_GICH_HCR_Type_VGrp0DIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_GICH_HCR_Type_VGrp0DIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_HCR_Type_VGrp0DIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_HCR_EL2_Type_VGrp0EIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_ICH_HCR_EL2_Type_VGrp0EIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_GICH_HCR_Type_VGrp0EIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_GICH_HCR_Type_VGrp0EIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_HCR_Type_VGrp0EIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_HCR_EL2_Type_VGrp1DIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_ICH_HCR_EL2_Type_VGrp1DIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_GICH_HCR_Type_VGrp1DIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_GICH_HCR_Type_VGrp1DIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_HCR_Type_VGrp1DIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_HCR_EL2_Type_VGrp1EIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_ICH_HCR_EL2_Type_VGrp1EIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_GICH_HCR_Type_VGrp1EIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_GICH_HCR_Type_VGrp1EIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_HCR_Type_VGrp1EIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_HCR_EL2_Type_vSGIEOICount (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_ICH_HCR_EL2_Type_vSGIEOICount (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_ICH_HCR_Type_vSGIEOICount (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def undefined_ICC_IGRPEN0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_IGRPEN0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTHPS_TVAL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHPS_TVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICC_EOIR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_EOIR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_AA64MMFR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64MMFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64MMFR0_EL1_Type_ASIDBits (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_AA64MMFR0_EL1_Type_ASIDBits (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_AA64MMFR0_EL1_Type_BigEnd (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_AA64MMFR0_EL1_Type_BigEnd (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_AA64MMFR0_EL1_Type_BigEndEL0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64MMFR0_EL1_Type_BigEndEL0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_AA64MMFR0_EL1_Type_ExS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _update_ID_AA64MMFR0_EL1_Type_ExS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _get_ID_AA64MMFR0_EL1_Type_FGT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _update_ID_AA64MMFR0_EL1_Type_FGT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _get_ID_AA64MMFR0_EL1_Type_PARange (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_AA64MMFR0_EL1_Type_PARange (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_AA64MMFR0_EL1_Type_SNSMem (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_AA64MMFR0_EL1_Type_SNSMem (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_AA64MMFR0_EL1_Type_TGran16 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_AA64MMFR0_EL1_Type_TGran16 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_AA64MMFR0_EL1_Type_TGran16_2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_ID_AA64MMFR0_EL1_Type_TGran16_2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_ID_AA64MMFR0_EL1_Type_TGran4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_AA64MMFR0_EL1_Type_TGran4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_AA64MMFR0_EL1_Type_TGran4_2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _update_ID_AA64MMFR0_EL1_Type_TGran4_2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _get_ID_AA64MMFR0_EL1_Type_TGran64 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_AA64MMFR0_EL1_Type_TGran64 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_AA64MMFR0_EL1_Type_TGran64_2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _update_ID_AA64MMFR0_EL1_Type_TGran64_2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def __set_PMCR_EL0 (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMCR_EL0_Type := value_name
  writeReg PMCR_EL0 (BitVec.update (← readReg PMCR_EL0) 0 (Bit (BitVec.slice r 0 1)))
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 15 3 (BitVec.slice r 3 13))
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 63 32 (BitVec.slice r 32 32))
  if ((! (! (← (IsFeatureImplemented FEAT_PMUv3p7)))) : Bool)
  then writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 31 24 (_get_PMCR_EL0_Type_IMP r))
  else (pure ())
  if ((! ((_get_PMCR_EL0_Type_IMP (← readReg PMCR_EL0)) != 0b00000000#8)) : Bool)
  then writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 23 16 (_get_PMCR_EL0_Type_IDCODE r))
  else (pure ())
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 2 2 (_get_PMCR_EL0_Type_C r))
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 1 1 (_get_PMCR_EL0_Type_P r))

def undefined_HDFGRTR2_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HDFGRTR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HDFGRTR2_EL2_Type_nPMSSDATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_HDFGRTR2_EL2_Type_nPMSSDATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_HDFGRTR2_EL2_Type_nSPMDEVAFF_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_HDFGRTR2_EL2_Type_nSPMDEVAFF_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_HDFGRTR2_EL2_Type_nSPMID (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_HDFGRTR2_EL2_Type_nSPMID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def undefined_VMPIDR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VMPIDR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_VMPIDR_EL2_Type_Aff0 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_VMPIDR_EL2_Type_Aff0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MPIDR_EL1_Type_Aff0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_MPIDR_EL1_Type_Aff0 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_MPIDR_Type_Aff0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_VMPIDR_Type_Aff0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def undefined_ID_AA64MMFR3_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64MMFR3_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64MMFR3_EL1_Type_ADERR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _update_ID_AA64MMFR3_EL1_Type_ADERR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _get_ID_AA64MMFR3_EL1_Type_ANERR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _update_ID_AA64MMFR3_EL1_Type_ANERR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _get_ID_AA64MMFR3_EL1_Type_D128_2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _update_ID_AA64MMFR3_EL1_Type_D128_2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _get_ID_AA64MMFR3_EL1_Type_MEC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_AA64MMFR3_EL1_Type_MEC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_AA64MMFR3_EL1_Type_S1PIE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_AA64MMFR3_EL1_Type_S1PIE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_AA64MMFR3_EL1_Type_S1POE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64MMFR3_EL1_Type_S1POE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_AA64MMFR3_EL1_Type_SCTLRX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_AA64MMFR3_EL1_Type_SCTLRX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_AA64MMFR3_EL1_Type_SDERR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64MMFR3_EL1_Type_SDERR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _get_ID_AA64MMFR3_EL1_Type_SNERR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _update_ID_AA64MMFR3_EL1_Type_SNERR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _get_ID_AA64MMFR3_EL1_Type_Spec_FPACC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _update_ID_AA64MMFR3_EL1_Type_Spec_FPACC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _get_ID_AA64MMFR3_EL1_Type_TCRX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_AA64MMFR3_EL1_Type_TCRX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def undefined_ICH_VTR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICH_VTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICH_VTR_EL2_Type_ListRegs (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _update_ICH_VTR_EL2_Type_ListRegs (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_GICH_VTR_Type_ListRegs (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_ICH_VTR_Type_ListRegs (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _get_GICH_VTR_Type_ListRegs (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_ICH_VTR_Type_ListRegs (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_ICH_VTR_EL2_Type_PREbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 28 26)

def _update_ICH_VTR_EL2_Type_PREbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 26 x)

def _update_GICH_VTR_Type_PREbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 26 x)

def _update_ICH_VTR_Type_PREbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 26 x)

def _get_GICH_VTR_Type_PREbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 28 26)

def _get_ICH_VTR_Type_PREbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 28 26)

def _get_ICH_VTR_EL2_Type_TDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_ICH_VTR_EL2_Type_TDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ICH_VTR_Type_TDS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_ICH_VTR_Type_TDS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_ICH_VTR_EL2_Type_nV4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_ICH_VTR_EL2_Type_nV4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_ICH_VTR_Type_nV4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_ICH_VTR_Type_nV4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def undefined_ID_PFR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_PFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_PFR1_EL1_Type_GenTimer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_PFR1_EL1_Type_GenTimer (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_PFR1_Type_GenTimer (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_PFR1_EL1_Type_MProgMod (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_PFR1_EL1_Type_MProgMod (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_PFR1_Type_MProgMod (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_PFR1_EL1_Type_ProgMod (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_PFR1_EL1_Type_ProgMod (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_PFR1_Type_ProgMod (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_PFR1_EL1_Type_Sec_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_PFR1_EL1_Type_Sec_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_PFR1_Type_Sec_frac (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_PFR1_EL1_Type_Security (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_PFR1_EL1_Type_Security (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_PFR1_Type_Security (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_PFR1_EL1_Type_Virt_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_PFR1_EL1_Type_Virt_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_PFR1_Type_Virt_frac (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_PFR1_EL1_Type_Virtualization (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_PFR1_EL1_Type_Virtualization (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_PFR1_Type_Virtualization (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def DBGDTR_EL0_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : DBGDTR_EL0_Type := value_name
  if ((← (__IMPDEF_boolean "read")) : Bool)
  then writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRTX_EL0) 31 0 (BitVec.slice r 32 32))
  else
    (do
      if ((← (__IMPDEF_boolean "read")) : Bool)
      then writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRTX_EL0) 31 0 (BitVec.slice r 32 32))
      else writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRRX_EL0) 31 0 (BitVec.slice r 32 32)))
  if ((← (__IMPDEF_boolean "read")) : Bool)
  then writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRRX_EL0) 31 0 (BitVec.slice r 0 32))
  else
    (do
      if ((← (__IMPDEF_boolean "read")) : Bool)
      then writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRRX_EL0) 31 0 (BitVec.slice r 0 32))
      else writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRTX_EL0) 31 0 (BitVec.slice r 0 32)))
  writeReg _DBGDTR_EL0 r

def undefined_ICV_EOIR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_EOIR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_DFR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_DFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_RNDRRS_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_RNDRRS_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_RNDRRS_Type_RNDRRS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_RNDRRS_Type_RNDRRS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def undefined_LORN_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_LORN_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_LORN_EL1_Type_Num (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_LORN_EL1_Type_Num (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def undefined_ICV_IGRPEN0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_IGRPEN0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CCSIDR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_CCSIDR_EL1_Type_Associativity (v : (BitVec 64)) : (BitVec 21) :=
  (Sail.BitVec.extractLsb v 23 3)

def _update_CCSIDR_EL1_Type_Associativity (v : (BitVec 64)) (x : (BitVec 21)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 3 x)

def _get_CCSIDR_Type_Associativity (v : (BitVec 32)) : (BitVec 21) :=
  (Sail.BitVec.extractLsb v 23 3)

def _get_CCSIDR_EL1_Type_LineSize (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _update_CCSIDR_EL1_Type_LineSize (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _get_CCSIDR_Type_LineSize (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def undefined_SMPRIMAP_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SMPRIMAP_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_RNDR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_RNDR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_HFGRTR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HFGRTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HFGRTR_EL2_Type_AIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_HFGRTR_EL2_Type_AIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_HFGRTR_EL2_Type_CCSIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_HFGRTR_EL2_Type_CCSIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_HFGRTR_EL2_Type_CLIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_HFGRTR_EL2_Type_CLIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_HFGRTR_EL2_Type_CTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_HFGRTR_EL2_Type_CTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_HFGRTR_EL2_Type_DCZID_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_HFGRTR_EL2_Type_DCZID_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_HFGRTR_EL2_Type_ERRIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _update_HFGRTR_EL2_Type_ERRIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _get_HFGRTR_EL2_Type_ERXFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)

def _update_HFGRTR_EL2_Type_ERXFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _get_HFGRTR_EL2_Type_ERXPFGF_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _update_HFGRTR_EL2_Type_ERXPFGF_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _get_HFGRTR_EL2_Type_ISR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_HFGRTR_EL2_Type_ISR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_HFGRTR_EL2_Type_LORID_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_HFGRTR_EL2_Type_LORID_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_HFGRTR_EL2_Type_MIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_HFGRTR_EL2_Type_MIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_HFGRTR_EL2_Type_MPIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_HFGRTR_EL2_Type_MPIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_HFGRTR_EL2_Type_REVIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_HFGRTR_EL2_Type_REVIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def undefined_ID_DFR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_DFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_ID_DFR0_EL1_Type_CopDbg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_DFR0_EL1_Type_CopSDbg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_DFR0_EL1_Type_CopSDbg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_DFR0_Type_CopSDbg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_DFR0_EL1_Type_CopTrc (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_DFR0_EL1_Type_CopTrc (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_DFR0_Type_CopTrc (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_DFR0_EL1_Type_MMapDbg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_DFR0_EL1_Type_MMapDbg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_DFR0_Type_MMapDbg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_DFR0_EL1_Type_MMapTrc (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_DFR0_EL1_Type_MMapTrc (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_DFR0_Type_MMapTrc (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_DFR0_EL1_Type_MProfDbg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_DFR0_EL1_Type_MProfDbg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_DFR0_Type_MProfDbg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_DFR0_EL1_Type_PerfMon (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_DFR0_EL1_Type_PerfMon (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_DFR0_Type_PerfMon (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def undefined_ICV_IGRPEN1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_IGRPEN1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMXEVCNTR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMXEVCNTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMXEVCNTR_EL0_Type_PMEVCNTR (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_PMXEVCNTR_EL0_Type_PMEVCNTR (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def undefined_HFGWTR2_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HFGWTR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICC_SGI1R_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_SGI1R_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MVFR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MVFR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MVFR2_EL1_Type_FPMisc (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_MVFR2_EL1_Type_FPMisc (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_MVFR2_Type_FPMisc (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_MVFR2_EL1_Type_SIMDMisc (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_MVFR2_EL1_Type_SIMDMisc (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_MVFR2_Type_SIMDMisc (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def undefined_DBGAUTHSTATUS_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DBGAUTHSTATUS_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_DBGAUTHSTATUS_EL1_Type_NSID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_DBGAUTHSTATUS_EL1_Type_NSID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_CTIAUTHSTATUS_Type_NSID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_DBGAUTHSTATUS_Type_NSID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_PMAUTHSTATUS_Type_NSID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _get_CTIAUTHSTATUS_Type_NSID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _get_DBGAUTHSTATUS_Type_NSID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _get_PMAUTHSTATUS_Type_NSID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _get_DBGAUTHSTATUS_EL1_Type_NSNID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _update_DBGAUTHSTATUS_EL1_Type_NSNID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _update_CTIAUTHSTATUS_Type_NSNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _update_DBGAUTHSTATUS_Type_NSNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _update_PMAUTHSTATUS_Type_NSNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _get_CTIAUTHSTATUS_Type_NSNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _get_DBGAUTHSTATUS_Type_NSNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _get_PMAUTHSTATUS_Type_NSNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _get_DBGAUTHSTATUS_EL1_Type_RLID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)

def _update_DBGAUTHSTATUS_EL1_Type_RLID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_PMAUTHSTATUS_Type_RLID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _get_PMAUTHSTATUS_Type_RLID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)

def _get_DBGAUTHSTATUS_EL1_Type_RLNID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _update_DBGAUTHSTATUS_EL1_Type_RLNID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_PMAUTHSTATUS_Type_RLNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _get_PMAUTHSTATUS_Type_RLNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _get_DBGAUTHSTATUS_EL1_Type_RTID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _update_DBGAUTHSTATUS_EL1_Type_RTID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _update_PMAUTHSTATUS_Type_RTID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _get_PMAUTHSTATUS_Type_RTID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _get_DBGAUTHSTATUS_EL1_Type_RTNID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)

def _update_DBGAUTHSTATUS_EL1_Type_RTNID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _update_PMAUTHSTATUS_Type_RTNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _get_PMAUTHSTATUS_Type_RTNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)

def _get_DBGAUTHSTATUS_EL1_Type_SID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _update_DBGAUTHSTATUS_EL1_Type_SID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_DBGAUTHSTATUS_Type_SID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_PMAUTHSTATUS_Type_SID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _get_DBGAUTHSTATUS_Type_SID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_PMAUTHSTATUS_Type_SID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_DBGAUTHSTATUS_EL1_Type_SNID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _update_DBGAUTHSTATUS_EL1_Type_SNID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_DBGAUTHSTATUS_Type_SNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_PMAUTHSTATUS_Type_SNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _get_DBGAUTHSTATUS_Type_SNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _get_PMAUTHSTATUS_Type_SNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def undefined_ICC_SRE_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_SRE_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_MMFR3_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_MMFR3_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_MMFR3_EL1_Type_BPMaint (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_MMFR3_EL1_Type_BPMaint (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_MMFR3_Type_BPMaint (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_MMFR3_EL1_Type_CMaintSW (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_MMFR3_EL1_Type_CMaintSW (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_MMFR3_Type_CMaintSW (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_MMFR3_EL1_Type_CMaintVA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_MMFR3_EL1_Type_CMaintVA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_MMFR3_Type_CMaintVA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_MMFR3_EL1_Type_CMemSz (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_MMFR3_EL1_Type_CMemSz (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_MMFR3_Type_CMemSz (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_MMFR3_EL1_Type_CohWalk (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_MMFR3_EL1_Type_CohWalk (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_MMFR3_Type_CohWalk (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_MMFR3_EL1_Type_MaintBcst (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_MMFR3_EL1_Type_MaintBcst (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_MMFR3_Type_MaintBcst (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_MMFR3_EL1_Type_Supersec (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_MMFR3_EL1_Type_Supersec (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_MMFR3_Type_Supersec (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def undefined_HDFGWTR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HDFGWTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HDFGWTR_EL2_Type_OSLAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_HDFGWTR_EL2_Type_OSLAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_HDFGWTR_EL2_Type_PMCR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_HDFGWTR_EL2_Type_PMCR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_HDFGWTR_EL2_Type_PMSWINC_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_HDFGWTR_EL2_Type_PMSWINC_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_HDFGWTR_EL2_Type_TRCOSLAR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)

def _update_HDFGWTR_EL2_Type_TRCOSLAR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _get_HDFGWTR_EL2_Type_TRFCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _update_HDFGWTR_EL2_Type_TRFCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def undefined_PMCEID1_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_PMCEID1_EL0_Type_ID0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_PMCEID1_EL0_Type_ID0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMCEID0_EL0_Type_ID0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMCEID0_Type_ID0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMCEID1_Type_ID0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_PMCEID0_EL0_Type_ID0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMCEID0_Type_ID0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMCEID1_Type_ID0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMCEID1_EL0_Type_ID1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_PMCEID1_EL0_Type_ID1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMCEID0_EL0_Type_ID1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMCEID0_Type_ID1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMCEID1_Type_ID1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_PMCEID0_EL0_Type_ID1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMCEID0_Type_ID1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMCEID1_Type_ID1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMCEID1_EL0_Type_ID10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_PMCEID1_EL0_Type_ID10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMCEID0_EL0_Type_ID10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMCEID0_Type_ID10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMCEID1_Type_ID10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_PMCEID0_EL0_Type_ID10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMCEID0_Type_ID10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMCEID1_Type_ID10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMCEID1_EL0_Type_ID11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_PMCEID1_EL0_Type_ID11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMCEID0_EL0_Type_ID11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMCEID0_Type_ID11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMCEID1_Type_ID11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_PMCEID0_EL0_Type_ID11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMCEID0_Type_ID11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMCEID1_Type_ID11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMCEID1_EL0_Type_ID12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_PMCEID1_EL0_Type_ID12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMCEID0_EL0_Type_ID12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMCEID0_Type_ID12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMCEID1_Type_ID12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_PMCEID0_EL0_Type_ID12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMCEID0_Type_ID12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMCEID1_Type_ID12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMCEID1_EL0_Type_ID13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_PMCEID1_EL0_Type_ID13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMCEID0_EL0_Type_ID13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMCEID0_Type_ID13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMCEID1_Type_ID13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_PMCEID0_EL0_Type_ID13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMCEID0_Type_ID13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMCEID1_Type_ID13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMCEID1_EL0_Type_ID14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_PMCEID1_EL0_Type_ID14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMCEID0_EL0_Type_ID14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMCEID0_Type_ID14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMCEID1_Type_ID14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_PMCEID0_EL0_Type_ID14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMCEID0_Type_ID14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMCEID1_Type_ID14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMCEID1_EL0_Type_ID15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_PMCEID1_EL0_Type_ID15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMCEID0_EL0_Type_ID15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMCEID0_Type_ID15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMCEID1_Type_ID15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_PMCEID0_EL0_Type_ID15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMCEID0_Type_ID15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMCEID1_Type_ID15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMCEID1_EL0_Type_ID16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_PMCEID1_EL0_Type_ID16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMCEID0_EL0_Type_ID16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMCEID0_Type_ID16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMCEID1_Type_ID16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_PMCEID0_EL0_Type_ID16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMCEID0_Type_ID16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMCEID1_Type_ID16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMCEID1_EL0_Type_ID17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_PMCEID1_EL0_Type_ID17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMCEID0_EL0_Type_ID17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMCEID0_Type_ID17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMCEID1_Type_ID17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_PMCEID0_EL0_Type_ID17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMCEID0_Type_ID17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMCEID1_Type_ID17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMCEID1_EL0_Type_ID18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_PMCEID1_EL0_Type_ID18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMCEID0_EL0_Type_ID18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMCEID0_Type_ID18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMCEID1_Type_ID18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_PMCEID0_EL0_Type_ID18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMCEID0_Type_ID18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMCEID1_Type_ID18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMCEID1_EL0_Type_ID19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_PMCEID1_EL0_Type_ID19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMCEID0_EL0_Type_ID19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMCEID0_Type_ID19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMCEID1_Type_ID19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_PMCEID0_EL0_Type_ID19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMCEID0_Type_ID19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMCEID1_Type_ID19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMCEID1_EL0_Type_ID2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_PMCEID1_EL0_Type_ID2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMCEID0_EL0_Type_ID2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMCEID0_Type_ID2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMCEID1_Type_ID2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_PMCEID0_EL0_Type_ID2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMCEID0_Type_ID2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMCEID1_Type_ID2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMCEID1_EL0_Type_ID20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_PMCEID1_EL0_Type_ID20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMCEID0_EL0_Type_ID20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMCEID0_Type_ID20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMCEID1_Type_ID20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_PMCEID0_EL0_Type_ID20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMCEID0_Type_ID20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMCEID1_Type_ID20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMCEID1_EL0_Type_ID21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_PMCEID1_EL0_Type_ID21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMCEID0_EL0_Type_ID21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMCEID0_Type_ID21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMCEID1_Type_ID21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_PMCEID0_EL0_Type_ID21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMCEID0_Type_ID21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMCEID1_Type_ID21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMCEID1_EL0_Type_ID22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_PMCEID1_EL0_Type_ID22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMCEID0_EL0_Type_ID22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMCEID0_Type_ID22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMCEID1_Type_ID22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_PMCEID0_EL0_Type_ID22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMCEID0_Type_ID22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMCEID1_Type_ID22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMCEID1_EL0_Type_ID23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_PMCEID1_EL0_Type_ID23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMCEID0_EL0_Type_ID23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMCEID0_Type_ID23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMCEID1_Type_ID23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_PMCEID0_EL0_Type_ID23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMCEID0_Type_ID23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMCEID1_Type_ID23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMCEID1_EL0_Type_ID24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_PMCEID1_EL0_Type_ID24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMCEID0_EL0_Type_ID24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMCEID0_Type_ID24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMCEID1_Type_ID24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_PMCEID0_EL0_Type_ID24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMCEID0_Type_ID24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMCEID1_Type_ID24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMCEID1_EL0_Type_ID25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_PMCEID1_EL0_Type_ID25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMCEID0_EL0_Type_ID25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMCEID0_Type_ID25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMCEID1_Type_ID25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_PMCEID0_EL0_Type_ID25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMCEID0_Type_ID25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMCEID1_Type_ID25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMCEID1_EL0_Type_ID26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_PMCEID1_EL0_Type_ID26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMCEID0_EL0_Type_ID26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMCEID0_Type_ID26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMCEID1_Type_ID26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_PMCEID0_EL0_Type_ID26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMCEID0_Type_ID26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMCEID1_Type_ID26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMCEID1_EL0_Type_ID27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_PMCEID1_EL0_Type_ID27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMCEID0_EL0_Type_ID27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMCEID0_Type_ID27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMCEID1_Type_ID27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_PMCEID0_EL0_Type_ID27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMCEID0_Type_ID27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMCEID1_Type_ID27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMCEID1_EL0_Type_ID28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_PMCEID1_EL0_Type_ID28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMCEID0_EL0_Type_ID28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMCEID0_Type_ID28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMCEID1_Type_ID28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_PMCEID0_EL0_Type_ID28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMCEID0_Type_ID28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMCEID1_Type_ID28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMCEID1_EL0_Type_ID29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_PMCEID1_EL0_Type_ID29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMCEID0_EL0_Type_ID29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMCEID0_Type_ID29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMCEID1_Type_ID29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_PMCEID0_EL0_Type_ID29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCEID0_Type_ID29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCEID1_Type_ID29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCEID1_EL0_Type_ID3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_PMCEID1_EL0_Type_ID3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMCEID0_EL0_Type_ID3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMCEID0_Type_ID3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMCEID1_Type_ID3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_PMCEID0_EL0_Type_ID3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMCEID0_Type_ID3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMCEID1_Type_ID3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMCEID1_EL0_Type_ID30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_PMCEID1_EL0_Type_ID30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMCEID0_EL0_Type_ID30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMCEID0_Type_ID30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMCEID1_Type_ID30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_PMCEID0_EL0_Type_ID30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMCEID0_Type_ID30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMCEID1_Type_ID30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMCEID1_EL0_Type_ID31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_PMCEID1_EL0_Type_ID31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCEID0_EL0_Type_ID31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCEID0_Type_ID31 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCEID1_Type_ID31 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_PMCEID0_EL0_Type_ID31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCEID0_Type_ID31 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCEID1_Type_ID31 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCEID1_EL0_Type_ID4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_PMCEID1_EL0_Type_ID4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCEID0_EL0_Type_ID4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCEID0_Type_ID4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCEID1_Type_ID4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_PMCEID0_EL0_Type_ID4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMCEID0_Type_ID4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMCEID1_Type_ID4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMCEID1_EL0_Type_ID5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_PMCEID1_EL0_Type_ID5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMCEID0_EL0_Type_ID5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMCEID0_Type_ID5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMCEID1_Type_ID5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_PMCEID0_EL0_Type_ID5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMCEID0_Type_ID5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMCEID1_Type_ID5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMCEID1_EL0_Type_ID6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_PMCEID1_EL0_Type_ID6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMCEID0_EL0_Type_ID6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMCEID0_Type_ID6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMCEID1_Type_ID6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_PMCEID0_EL0_Type_ID6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMCEID0_Type_ID6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMCEID1_Type_ID6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMCEID1_EL0_Type_ID7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_PMCEID1_EL0_Type_ID7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMCEID0_EL0_Type_ID7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMCEID0_Type_ID7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMCEID1_Type_ID7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_PMCEID0_EL0_Type_ID7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMCEID0_Type_ID7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMCEID1_Type_ID7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMCEID1_EL0_Type_ID8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_PMCEID1_EL0_Type_ID8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMCEID0_EL0_Type_ID8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMCEID0_Type_ID8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMCEID1_Type_ID8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_PMCEID0_EL0_Type_ID8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMCEID0_Type_ID8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMCEID1_Type_ID8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMCEID1_EL0_Type_ID9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_PMCEID1_EL0_Type_ID9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMCEID0_EL0_Type_ID9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMCEID0_Type_ID9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMCEID1_Type_ID9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_PMCEID0_EL0_Type_ID9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMCEID0_Type_ID9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMCEID1_Type_ID9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMCEID1_EL0_Type_IDhi0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_PMCEID1_EL0_Type_IDhi0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMCEID0_EL0_Type_IDhi0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMCEID2_Type_IDhi0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMCEID3_Type_IDhi0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_PMCEID0_EL0_Type_IDhi0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMCEID2_Type_IDhi0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMCEID3_Type_IDhi0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMCEID1_EL0_Type_IDhi1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_PMCEID1_EL0_Type_IDhi1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_PMCEID0_EL0_Type_IDhi1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_PMCEID2_Type_IDhi1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMCEID3_Type_IDhi1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_PMCEID0_EL0_Type_IDhi1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _get_PMCEID2_Type_IDhi1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMCEID3_Type_IDhi1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMCEID1_EL0_Type_IDhi10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)

def _update_PMCEID1_EL0_Type_IDhi10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_PMCEID0_EL0_Type_IDhi10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_PMCEID2_Type_IDhi10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMCEID3_Type_IDhi10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_PMCEID0_EL0_Type_IDhi10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)

def _get_PMCEID2_Type_IDhi10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMCEID3_Type_IDhi10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMCEID1_EL0_Type_IDhi11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _update_PMCEID1_EL0_Type_IDhi11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_PMCEID0_EL0_Type_IDhi11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_PMCEID2_Type_IDhi11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMCEID3_Type_IDhi11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_PMCEID0_EL0_Type_IDhi11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _get_PMCEID2_Type_IDhi11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMCEID3_Type_IDhi11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMCEID1_EL0_Type_IDhi12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _update_PMCEID1_EL0_Type_IDhi12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_PMCEID0_EL0_Type_IDhi12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_PMCEID2_Type_IDhi12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMCEID3_Type_IDhi12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_PMCEID0_EL0_Type_IDhi12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _get_PMCEID2_Type_IDhi12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMCEID3_Type_IDhi12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMCEID1_EL0_Type_IDhi13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _update_PMCEID1_EL0_Type_IDhi13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_PMCEID0_EL0_Type_IDhi13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_PMCEID2_Type_IDhi13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMCEID3_Type_IDhi13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_PMCEID0_EL0_Type_IDhi13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _get_PMCEID2_Type_IDhi13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMCEID3_Type_IDhi13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMCEID1_EL0_Type_IDhi14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _update_PMCEID1_EL0_Type_IDhi14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_PMCEID0_EL0_Type_IDhi14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_PMCEID2_Type_IDhi14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMCEID3_Type_IDhi14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_PMCEID0_EL0_Type_IDhi14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _get_PMCEID2_Type_IDhi14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMCEID3_Type_IDhi14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMCEID1_EL0_Type_IDhi15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _update_PMCEID1_EL0_Type_IDhi15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _update_PMCEID0_EL0_Type_IDhi15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _update_PMCEID2_Type_IDhi15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMCEID3_Type_IDhi15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_PMCEID0_EL0_Type_IDhi15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _get_PMCEID2_Type_IDhi15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMCEID3_Type_IDhi15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMCEID1_EL0_Type_IDhi16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_PMCEID1_EL0_Type_IDhi16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_PMCEID0_EL0_Type_IDhi16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_PMCEID2_Type_IDhi16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMCEID3_Type_IDhi16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_PMCEID0_EL0_Type_IDhi16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _get_PMCEID2_Type_IDhi16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMCEID3_Type_IDhi16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMCEID1_EL0_Type_IDhi17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _update_PMCEID1_EL0_Type_IDhi17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _update_PMCEID0_EL0_Type_IDhi17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _update_PMCEID2_Type_IDhi17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMCEID3_Type_IDhi17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_PMCEID0_EL0_Type_IDhi17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _get_PMCEID2_Type_IDhi17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMCEID3_Type_IDhi17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMCEID1_EL0_Type_IDhi18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _update_PMCEID1_EL0_Type_IDhi18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_PMCEID0_EL0_Type_IDhi18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_PMCEID2_Type_IDhi18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMCEID3_Type_IDhi18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_PMCEID0_EL0_Type_IDhi18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _get_PMCEID2_Type_IDhi18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMCEID3_Type_IDhi18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMCEID1_EL0_Type_IDhi19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)

def _update_PMCEID1_EL0_Type_IDhi19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_PMCEID0_EL0_Type_IDhi19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_PMCEID2_Type_IDhi19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMCEID3_Type_IDhi19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_PMCEID0_EL0_Type_IDhi19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)

def _get_PMCEID2_Type_IDhi19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMCEID3_Type_IDhi19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMCEID1_EL0_Type_IDhi2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _update_PMCEID1_EL0_Type_IDhi2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_PMCEID0_EL0_Type_IDhi2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_PMCEID2_Type_IDhi2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMCEID3_Type_IDhi2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_PMCEID0_EL0_Type_IDhi2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _get_PMCEID2_Type_IDhi2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMCEID3_Type_IDhi2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMCEID1_EL0_Type_IDhi20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _update_PMCEID1_EL0_Type_IDhi20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_PMCEID0_EL0_Type_IDhi20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_PMCEID2_Type_IDhi20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMCEID3_Type_IDhi20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_PMCEID0_EL0_Type_IDhi20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _get_PMCEID2_Type_IDhi20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMCEID3_Type_IDhi20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMCEID1_EL0_Type_IDhi21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _update_PMCEID1_EL0_Type_IDhi21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_PMCEID0_EL0_Type_IDhi21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_PMCEID2_Type_IDhi21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMCEID3_Type_IDhi21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_PMCEID0_EL0_Type_IDhi21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _get_PMCEID2_Type_IDhi21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMCEID3_Type_IDhi21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMCEID1_EL0_Type_IDhi22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _update_PMCEID1_EL0_Type_IDhi22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_PMCEID0_EL0_Type_IDhi22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_PMCEID2_Type_IDhi22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMCEID3_Type_IDhi22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_PMCEID0_EL0_Type_IDhi22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _get_PMCEID2_Type_IDhi22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMCEID3_Type_IDhi22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMCEID1_EL0_Type_IDhi23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _update_PMCEID1_EL0_Type_IDhi23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_PMCEID0_EL0_Type_IDhi23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_PMCEID2_Type_IDhi23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMCEID3_Type_IDhi23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_PMCEID0_EL0_Type_IDhi23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _get_PMCEID2_Type_IDhi23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMCEID3_Type_IDhi23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMCEID1_EL0_Type_IDhi24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _update_PMCEID1_EL0_Type_IDhi24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _update_PMCEID0_EL0_Type_IDhi24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _update_PMCEID2_Type_IDhi24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMCEID3_Type_IDhi24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_PMCEID0_EL0_Type_IDhi24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _get_PMCEID2_Type_IDhi24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMCEID3_Type_IDhi24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMCEID1_EL0_Type_IDhi25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _update_PMCEID1_EL0_Type_IDhi25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_PMCEID0_EL0_Type_IDhi25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_PMCEID2_Type_IDhi25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMCEID3_Type_IDhi25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_PMCEID0_EL0_Type_IDhi25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _get_PMCEID2_Type_IDhi25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMCEID3_Type_IDhi25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMCEID1_EL0_Type_IDhi26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_PMCEID1_EL0_Type_IDhi26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_PMCEID0_EL0_Type_IDhi26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_PMCEID2_Type_IDhi26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMCEID3_Type_IDhi26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_PMCEID0_EL0_Type_IDhi26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _get_PMCEID2_Type_IDhi26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMCEID3_Type_IDhi26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMCEID1_EL0_Type_IDhi27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_PMCEID1_EL0_Type_IDhi27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_PMCEID0_EL0_Type_IDhi27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_PMCEID2_Type_IDhi27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMCEID3_Type_IDhi27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_PMCEID0_EL0_Type_IDhi27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _get_PMCEID2_Type_IDhi27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMCEID3_Type_IDhi27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMCEID1_EL0_Type_IDhi28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_PMCEID1_EL0_Type_IDhi28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_PMCEID0_EL0_Type_IDhi28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_PMCEID2_Type_IDhi28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMCEID3_Type_IDhi28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_PMCEID0_EL0_Type_IDhi28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _get_PMCEID2_Type_IDhi28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMCEID3_Type_IDhi28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMCEID1_EL0_Type_IDhi29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _update_PMCEID1_EL0_Type_IDhi29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_PMCEID0_EL0_Type_IDhi29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_PMCEID2_Type_IDhi29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMCEID3_Type_IDhi29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_PMCEID0_EL0_Type_IDhi29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_PMCEID2_Type_IDhi29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCEID3_Type_IDhi29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCEID1_EL0_Type_IDhi3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _update_PMCEID1_EL0_Type_IDhi3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_PMCEID0_EL0_Type_IDhi3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_PMCEID2_Type_IDhi3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMCEID3_Type_IDhi3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_PMCEID0_EL0_Type_IDhi3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _get_PMCEID2_Type_IDhi3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMCEID3_Type_IDhi3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMCEID1_EL0_Type_IDhi30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_PMCEID1_EL0_Type_IDhi30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_PMCEID0_EL0_Type_IDhi30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_PMCEID2_Type_IDhi30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMCEID3_Type_IDhi30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_PMCEID0_EL0_Type_IDhi30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_PMCEID2_Type_IDhi30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMCEID3_Type_IDhi30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMCEID1_EL0_Type_IDhi31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_PMCEID1_EL0_Type_IDhi31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_PMCEID0_EL0_Type_IDhi31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_PMCEID2_Type_IDhi31 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCEID3_Type_IDhi31 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_PMCEID0_EL0_Type_IDhi31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_PMCEID2_Type_IDhi31 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCEID3_Type_IDhi31 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCEID1_EL0_Type_IDhi4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_PMCEID1_EL0_Type_IDhi4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_PMCEID0_EL0_Type_IDhi4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_PMCEID2_Type_IDhi4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCEID3_Type_IDhi4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_PMCEID0_EL0_Type_IDhi4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _get_PMCEID2_Type_IDhi4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMCEID3_Type_IDhi4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMCEID1_EL0_Type_IDhi5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_PMCEID1_EL0_Type_IDhi5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_PMCEID0_EL0_Type_IDhi5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_PMCEID2_Type_IDhi5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMCEID3_Type_IDhi5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_PMCEID0_EL0_Type_IDhi5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _get_PMCEID2_Type_IDhi5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMCEID3_Type_IDhi5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMCEID1_EL0_Type_IDhi6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)

def _update_PMCEID1_EL0_Type_IDhi6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_PMCEID0_EL0_Type_IDhi6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_PMCEID2_Type_IDhi6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMCEID3_Type_IDhi6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_PMCEID0_EL0_Type_IDhi6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)

def _get_PMCEID2_Type_IDhi6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMCEID3_Type_IDhi6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMCEID1_EL0_Type_IDhi7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _update_PMCEID1_EL0_Type_IDhi7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _update_PMCEID0_EL0_Type_IDhi7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _update_PMCEID2_Type_IDhi7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMCEID3_Type_IDhi7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_PMCEID0_EL0_Type_IDhi7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _get_PMCEID2_Type_IDhi7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMCEID3_Type_IDhi7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMCEID1_EL0_Type_IDhi8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _update_PMCEID1_EL0_Type_IDhi8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_PMCEID0_EL0_Type_IDhi8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_PMCEID2_Type_IDhi8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMCEID3_Type_IDhi8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_PMCEID0_EL0_Type_IDhi8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _get_PMCEID2_Type_IDhi8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMCEID3_Type_IDhi8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMCEID1_EL0_Type_IDhi9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _update_PMCEID1_EL0_Type_IDhi9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_PMCEID0_EL0_Type_IDhi9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_PMCEID2_Type_IDhi9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMCEID3_Type_IDhi9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_PMCEID0_EL0_Type_IDhi9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _get_PMCEID2_Type_IDhi9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMCEID3_Type_IDhi9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def undefined_CNTPS_TVAL_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTPS_TVAL_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICV_AP1R_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_AP1R_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_LOREA_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_LOREA_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTV_TVAL_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTV_TVAL_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICV_DIR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_DIR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICC_IAR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_IAR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MPIDR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_DBGCLAIMCLR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DBGCLAIMCLR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMCEID0_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_ICV_HPPIR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_HPPIR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_PFR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_PFR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SPMACCESSR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPMACCESSR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def __set_CNTHV_CTL_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTHV_CTL_EL2_Type := value_name
  writeReg CNTHV_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHV_CTL_EL2) 1 0 (BitVec.slice r 0 2))
  writeReg CNTHV_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHV_CTL_EL2) 63 3 (BitVec.slice r 3 61))

def undefined_ICC_EOIR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICC_EOIR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ID_AA64ZFR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64ZFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64ZFR0_EL1_Type_B16B16 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_AA64ZFR0_EL1_Type_B16B16 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_AA64SMFR0_EL1_Type_B16B16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _get_ID_AA64SMFR0_EL1_Type_B16B16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _get_ID_AA64ZFR0_EL1_Type_BitPerm (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64ZFR0_EL1_Type_BitPerm (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_AA64ZFR0_EL1_Type_F32MM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64ZFR0_EL1_Type_F32MM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _get_ID_AA64ZFR0_EL1_Type_F64MM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _update_ID_AA64ZFR0_EL1_Type_F64MM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _get_ID_AA64ZFR0_EL1_Type_SVEver (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_AA64ZFR0_EL1_Type_SVEver (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def undefined_ICC_SGI1R_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_ICC_SGI0R_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def CNTVOFF_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _CNTVOFF ) : SailM CNTVOFF_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (← readReg CNTVOFF_EL2) 0 64)))

def CNTVOFF_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTVOFF_Type := value_name
  writeReg CNTVOFF_EL2 (Sail.BitVec.updateSubrange (← readReg CNTVOFF_EL2) 63 0 (BitVec.slice r 0 64))
  writeReg _CNTVOFF r

def undefined_ICC_ASGI1R_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def CNTHP_CVAL_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTHP_CVAL_Type := value_name
  writeReg CNTHP_CVAL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHP_CVAL_EL2) 63 0 (BitVec.slice r 0 64))
  writeReg _CNTHP_CVAL r

def undefined_CNTV_CVAL_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTV_CVAL_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def CNTV_CVAL_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _CNTV_CVAL ) : SailM CNTV_CVAL_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (← readReg CNTV_CVAL_EL0) 0 64)))

def CNTV_CVAL_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTV_CVAL_Type := value_name
  writeReg CNTV_CVAL_EL0 (Sail.BitVec.updateSubrange (← readReg CNTV_CVAL_EL0) 63 0 (BitVec.slice r 0 64))
  writeReg _CNTV_CVAL r

def undefined_DBGDRAR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def CNTP_CVAL_NS_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTP_CVAL_Type := value_name
  writeReg CNTP_CVAL_EL0 (Sail.BitVec.updateSubrange (← readReg CNTP_CVAL_EL0) 63 0 (BitVec.slice r 0 64))
  writeReg _CNTP_CVAL_NS r

def undefined_ID_AA64SMFR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64SMFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64SMFR0_EL1_Type_B16F32 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _update_ID_AA64SMFR0_EL1_Type_B16F32 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _get_ID_AA64SMFR0_EL1_Type_BI32I32 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_ID_AA64SMFR0_EL1_Type_BI32I32 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _get_ID_AA64SMFR0_EL1_Type_F16F16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)

def _update_ID_AA64SMFR0_EL1_Type_F16F16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _get_ID_AA64SMFR0_EL1_Type_F16F32 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _update_ID_AA64SMFR0_EL1_Type_F16F32 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _get_ID_AA64SMFR0_EL1_Type_F32F32 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_ID_AA64SMFR0_EL1_Type_F32F32 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _get_ID_AA64SMFR0_EL1_Type_F64F64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_ID_AA64SMFR0_EL1_Type_F64F64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _get_ID_AA64SMFR0_EL1_Type_I16I32 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _update_ID_AA64SMFR0_EL1_Type_I16I32 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _get_ID_AA64SMFR0_EL1_Type_I16I64 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64SMFR0_EL1_Type_I16I64 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _get_ID_AA64SMFR0_EL1_Type_I8I32 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _update_ID_AA64SMFR0_EL1_Type_I8I32 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _get_ID_AA64SMFR0_EL1_Type_SMEver (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _update_ID_AA64SMFR0_EL1_Type_SMEver (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def __set_MPAM2_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM2_EL2_Type := value_name
  writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange (← readReg MPAM2_EL2) 53 0 (BitVec.slice r 0 54))
  writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange (← readReg MPAM2_EL2) 62 55 (BitVec.slice r 55 8))
  if ((! (HaveEL EL3)) : Bool)
  then writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange (← readReg MPAM2_EL2) 63 63 (_get_MPAM2_EL2_Type_MPAMEN r))
  else (pure ())

def undefined_GMID_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GMID_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_AMEVCNTR1_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMEVCNTR1_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_AMEVCNTR1_EL0_Type_ACNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_AMEVCNTR1_EL0_Type_ACNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_AMEVCNTR0_EL0_Type_ACNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_AMEVCNTR0_Type_ACNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_AMEVCNTR1_Type_ACNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _get_AMEVCNTR0_EL0_Type_ACNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_AMEVCNTR0_Type_ACNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_AMEVCNTR1_Type_ACNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def undefined_AMEVCNTR0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMEVCNTR0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_AMEVCNTR1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMEVCNTR1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def AMEVCNTR1_read (n : Nat) : SailM (BitVec 64) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _AMEVCNTR1) n)) ) : SailM AMEVCNTR1_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) n) 0 64)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def AMEVCNTR1_set (n : Nat) (value_name : (BitVec 64)) : SailM Unit := do
  let r : AMEVCNTR1_Type := value_name
  writeReg AMEVCNTR1_EL0 (vectorUpdate (← readReg AMEVCNTR1_EL0) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg AMEVCNTR1_EL0) n) 63 0 (BitVec.slice r 0 64)))
  writeReg _AMEVCNTR1 (vectorUpdate (← readReg _AMEVCNTR1) n r)

def undefined_AMCR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMCR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_AMCR_EL0_Type_CG1RZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_AMCR_EL0_Type_CG1RZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_AMCR_Type_CG1RZ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_AMCR_Type_CG1RZ (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def undefined_AMCNTENSET0_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMCNTENSET0_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_AMCNTENCLR0_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMCNTENCLR0_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_AMEVTYPER0_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMEVTYPER0_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_AMCNTENSET1_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMCNTENSET1_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_AMCNTENCLR1_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMCNTENCLR1_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_AMEVCNTR0_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMEVCNTR0_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def AMEVCNTR0_EL0_read (n : Nat) : SailM (BitVec 64) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _AMEVCNTR0_EL0) n)) ) : SailM AMEVCNTR0_EL0_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (GetElem?.getElem! (← readReg AMEVCNTR0) n) 0 64)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def AMEVCNTR0_EL0_set (n : Nat) (value_name : (BitVec 64)) : SailM Unit := do
  let r : AMEVCNTR0_EL0_Type := value_name
  writeReg AMEVCNTR0 (vectorUpdate (← readReg AMEVCNTR0) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg AMEVCNTR0) n) 63 0 (BitVec.slice r 0 64)))
  writeReg _AMEVCNTR0_EL0 (vectorUpdate (← readReg _AMEVCNTR0_EL0) n r)

def undefined_AMCFGR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMCFGR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_AMCFGR_EL0_Type_NCG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_AMCFGR_EL0_Type_NCG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_AMCFGR_Type_NCG (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_PMCFGR_Type_NCG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_AMCFGR_Type_NCG (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_PMCFGR_Type_NCG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_AMCFGR_EL0_Type_SIZE (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)

def _update_AMCFGR_EL0_Type_SIZE (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 8 x)

def _update_AMCFGR_Type_SIZE (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 8 x)

def _update_AMPIDR4_Type_SIZE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_CTIPIDR4_Type_SIZE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_EDPIDR4_Type_SIZE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PMCFGR_Type_SIZE (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 8 x)

def _update_PMPIDR4_Type_SIZE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_AMCFGR_Type_SIZE (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)

def _get_AMPIDR4_Type_SIZE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_CTIPIDR4_Type_SIZE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_EDPIDR4_Type_SIZE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_PMCFGR_Type_SIZE (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)

def _get_PMPIDR4_Type_SIZE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def undefined_AMUSERENR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMUSERENR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_AMCG1IDR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMCG1IDR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF10_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF10_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF110_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF110_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF111_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF111_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF112_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF112_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF113_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF113_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF114_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF114_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF115_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF115_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF11_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF11_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF12_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF12_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF13_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF13_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF14_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF14_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF15_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF15_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF16_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF16_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF17_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF17_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF18_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF18_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF19_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF19_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def undefined_AMEVTYPER1_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMEVTYPER1_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_AMCGCR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_AMCGCR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_AMCGCR_EL0_Type_CG0NC (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_AMCGCR_EL0_Type_CG0NC (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_AMCGCR_Type_CG0NC (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_PMCGCR0_Type_CG0NC (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_AMCGCR_Type_CG0NC (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_PMCGCR0_Type_CG0NC (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_AMCGCR_EL0_Type_CG1NC (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _update_AMCGCR_EL0_Type_CG1NC (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_AMCGCR_Type_CG1NC (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_PMCGCR0_Type_CG1NC (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _get_AMCGCR_Type_CG1NC (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_PMCGCR0_Type_CG1NC (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def undefined_ERRIDR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ERRIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_ERRIDR_EL1_Type_NUM (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_ERRIDR_Type_NUM (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_ERRIDR_Type_NUM (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def undefined_ERRSELR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ERRSELR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ERXGSR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ERXGSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_BRBINF_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBINF_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_BRBTGT_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBTGT_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_BRBSRC_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBSRC_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_GITS_CREADR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GITS_CREADR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_GITS_CREADR_Type_Offset (v : (BitVec 64)) : (BitVec 15) :=
  (Sail.BitVec.extractLsb v 19 5)

def _update_GITS_CREADR_Type_Offset (v : (BitVec 64)) (x : (BitVec 15)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 5 x)

def _update_GITS_CWRITER_Type_Offset (v : (BitVec 64)) (x : (BitVec 15)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 5 x)

def _get_GITS_CWRITER_Type_Offset (v : (BitVec 64)) : (BitVec 15) :=
  (Sail.BitVec.extractLsb v 19 5)

def _get_GITS_CREADR_Type_Stalled (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_GITS_CREADR_Type_Stalled (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def undefined_GICR_PENDBASER_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GICR_PENDBASER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_GICR_PENDBASER_Type_InnerCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 9 7)

def _update_GICR_PENDBASER_Type_InnerCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 7 x)

def _update_GICR_PROPBASER_Type_InnerCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 7 x)

def _update_GICR_VPENDBASER_Type_InnerCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 7 x)

def _update_GICR_VPROPBASER_Type_InnerCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 7 x)

def _update_GITS_CBASER_Type_InnerCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 59 x)

def _get_GICR_PROPBASER_Type_InnerCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 9 7)

def _get_GICR_VPENDBASER_Type_InnerCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 9 7)

def _get_GICR_VPROPBASER_Type_InnerCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 9 7)

def _get_GITS_CBASER_Type_InnerCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 61 59)

def _get_GICR_PENDBASER_Type_OuterCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 58 56)

def _update_GICR_PENDBASER_Type_OuterCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 56 x)

def _update_GICR_PROPBASER_Type_OuterCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 56 x)

def _update_GICR_VPENDBASER_Type_OuterCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 56 x)

def _update_GICR_VPROPBASER_Type_OuterCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 56 x)

def _update_GITS_CBASER_Type_OuterCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 53 x)

def _get_GICR_PROPBASER_Type_OuterCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 58 56)

def _get_GICR_VPENDBASER_Type_OuterCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 58 56)

def _get_GICR_VPROPBASER_Type_OuterCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 58 56)

def _get_GITS_CBASER_Type_OuterCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 55 53)

def _get_GICR_PENDBASER_Type_PTZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_GICR_PENDBASER_Type_PTZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _get_GICR_PENDBASER_Type_Physical_Address (v : (BitVec 64)) : (BitVec 36) :=
  (Sail.BitVec.extractLsb v 51 16)

def _update_GICR_PENDBASER_Type_Physical_Address (v : (BitVec 64)) (x : (BitVec 36)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 16 x)

def _update_GICR_PROPBASER_Type_Physical_Address (v : (BitVec 64)) (x : (BitVec 40)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 12 x)

def _update_GICR_VPENDBASER_Type_Physical_Address (v : (BitVec 64)) (x : (BitVec 36)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 16 x)

def _update_GICR_VPROPBASER_Type_Physical_Address (v : (BitVec 64)) (x : (BitVec 40)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 12 x)

def _update_GITS_CBASER_Type_Physical_Address (v : (BitVec 64)) (x : (BitVec 40)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 12 x)

def _get_GICR_PROPBASER_Type_Physical_Address (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)

def _get_GICR_VPENDBASER_Type_Physical_Address (v : (BitVec 64)) : (BitVec 36) :=
  (Sail.BitVec.extractLsb v 51 16)

def _get_GICR_VPROPBASER_Type_Physical_Address (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)

def _get_GITS_CBASER_Type_Physical_Address (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)

def _get_GICR_PENDBASER_Type_Shareability (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _update_GICR_PENDBASER_Type_Shareability (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_GICR_PROPBASER_Type_Shareability (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_GICR_VPENDBASER_Type_Shareability (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_GICR_VPROPBASER_Type_Shareability (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_GITS_CBASER_Type_Shareability (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _get_GICR_PROPBASER_Type_Shareability (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _get_GICR_VPENDBASER_Type_Shareability (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _get_GICR_VPROPBASER_Type_Shareability (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _get_GITS_CBASER_Type_Shareability (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def undefined_GICR_PROPBASER_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GICR_PROPBASER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_GICR_VPROPBASER_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GICR_VPROPBASER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_GICR_VPROPBASER_Type_Entry_Size (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 61 59)

def _update_GICR_VPROPBASER_Type_Entry_Size (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 59 x)

def _get_GICR_VPROPBASER_Type_Indirect (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _update_GICR_VPROPBASER_Type_Indirect (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _get_GICR_VPROPBASER_Type_Page_Size (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 54 53)

def _update_GICR_VPROPBASER_Type_Page_Size (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 53 x)

def _get_GICR_VPROPBASER_Type_Size (v : (BitVec 64)) : (BitVec 7) :=
  (Sail.BitVec.extractLsb v 6 0)

def _update_GICR_VPROPBASER_Type_Size (v : (BitVec 64)) (x : (BitVec 7)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 0 x)

def _update_GITS_CBASER_Type_Size (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_GITS_CBASER_Type_Size (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def undefined_EDPFR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_EDPFR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_GICR_CLRLPIR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GICR_CLRLPIR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_GICR_INVALLR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GICR_INVALLR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_GICR_INVALLR_Type_vPEID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _update_GICR_INVALLR_Type_vPEID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _update_GICR_INVLPIR_Type_vPEID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _update_GICR_VPENDBASER_Type_vPEID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_GICR_VSGIR_Type_vPEID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_GITS_SGIR_Type_vPEID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _get_GICR_INVLPIR_Type_vPEID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _get_GICR_VPENDBASER_Type_vPEID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_GICR_VSGIR_Type_vPEID (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_GITS_SGIR_Type_vPEID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def undefined_EDHSR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_EDHSR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_EDHSR_Type_FnP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_EDHSR_Type_FnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_EDHSR_Type_VNCR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_EDHSR_Type_VNCR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_EDHSR_Type_WPF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_EDHSR_Type_WPF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_EDHSR_Type_WPT (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 23 18)

def _update_EDHSR_Type_WPT (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 18 x)

def _get_EDHSR_Type_WPTV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_EDHSR_Type_WPTV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def undefined_EDPCSR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_EDPCSR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_GICR_VPENDBASER_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GICR_VPENDBASER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_GICR_VPENDBASER_Type_Dirty (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_GICR_VPENDBASER_Type_Dirty (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _get_GICR_VPENDBASER_Type_Doorbell (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_GICR_VPENDBASER_Type_Doorbell (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _get_GICR_VPENDBASER_Type_IDAI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_GICR_VPENDBASER_Type_IDAI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _get_GICR_VPENDBASER_Type_PendingLast (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _update_GICR_VPENDBASER_Type_PendingLast (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _get_GICR_VPENDBASER_Type_VGrp0En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_GICR_VPENDBASER_Type_VGrp0En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _get_GICR_VPENDBASER_Type_VGrp1En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_GICR_VPENDBASER_Type_VGrp1En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def undefined_GITS_TYPER_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GITS_TYPER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_GITS_TYPER_Type_CCT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_GITS_TYPER_Type_CCT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GITS_TYPER_Type_CIDbits (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_GITS_TYPER_Type_CIDbits (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_GITS_TYPER_Type_CIL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_GITS_TYPER_Type_CIL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _get_GITS_TYPER_Type_Devbits (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 17 13)

def _update_GITS_TYPER_Type_Devbits (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 13 x)

def _get_GITS_TYPER_Type_HCC (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _update_GITS_TYPER_Type_HCC (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _get_GITS_TYPER_Type_ID_bits (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 12 8)

def _update_GITS_TYPER_Type_ID_bits (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 8 x)

def _get_GITS_TYPER_Type_INV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _update_GITS_TYPER_Type_INV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _get_GITS_TYPER_Type_ITT_entry_size (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_GITS_TYPER_Type_ITT_entry_size (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_GITS_TYPER_Type_PTA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_GITS_TYPER_Type_PTA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_GITS_TYPER_Type_Physical (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_GITS_TYPER_Type_Physical (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GITS_TYPER_Type_SVPET (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 42 41)

def _update_GITS_TYPER_Type_SVPET (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 41 x)

def _get_GITS_TYPER_Type_UMSI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _update_GITS_TYPER_Type_UMSI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_GITS_STATUSR_Type_UMSI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_GITS_STATUSR_Type_UMSI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_GITS_TYPER_Type_UMSIirq (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _update_GITS_TYPER_Type_UMSIirq (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_GITS_CTLR_Type_UMSIirq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_GITS_CTLR_Type_UMSIirq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_GITS_TYPER_Type_VMAPP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _update_GITS_TYPER_Type_VMAPP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _get_GITS_TYPER_Type_VMOVP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_GITS_TYPER_Type_VMOVP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _get_GITS_TYPER_Type_VSGI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _update_GITS_TYPER_Type_VSGI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _get_GITS_TYPER_Type_Virtual (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_GITS_TYPER_Type_Virtual (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GITS_TYPER_Type_nID (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _update_GITS_TYPER_Type_nID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def undefined_GITS_SGIR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GITS_SGIR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_EDDFR1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_EDDFR1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_GITS_CWRITER_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GITS_CWRITER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_GITS_CWRITER_Type_Retry (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_GITS_CWRITER_Type_Retry (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def undefined_EDDFR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_EDDFR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_GICR_INVLPIR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GICR_INVLPIR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_EDAA32PFR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_EDAA32PFR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_EDAA32PFR_Type_MSA_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_EDAA32PFR_Type_MSA_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def undefined_GITS_CBASER_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GITS_CBASER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_GICR_SETLPIR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GICR_SETLPIR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMCFGR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMCFGR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMCFGR_Type_CCD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_PMCFGR_Type_CCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_PMCFGR_Type_NA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_PMCFGR_Type_NA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def undefined_PMCNTEN_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_PMIIDR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMIIDR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMIIDR_Type_ProductID (v : (BitVec 64)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 31 20)

def _update_PMIIDR_Type_ProductID (v : (BitVec 64)) (x : (BitVec 12)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 20 x)

def _update_AMIIDR_Type_ProductID (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 20 x)

def _update_GICD_IIDR_Type_ProductID (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_GICM_IIDR_Type_ProductID (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_GICR_IIDR_Type_ProductID (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_GITS_IIDR_Type_ProductID (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _get_AMIIDR_Type_ProductID (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 31 20)

def _get_GICD_IIDR_Type_ProductID (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_GICM_IIDR_Type_ProductID (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_GICR_IIDR_Type_ProductID (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_GITS_IIDR_Type_ProductID (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def undefined_PMINTEN_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_PMOVS_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_PMPCSCTL_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMPCSCTL_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMVCIDSR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMVCIDSR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ICH_ELRSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICC_IAR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def AIFSR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AIFSR_NS ) : SailM AIFSR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AFSR1_EL1) 0 32)))

def AIFSR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AIFSR_Type := value_name
  writeReg AFSR1_EL1 (Sail.BitVec.updateSubrange (← readReg AFSR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _AIFSR_NS r

def undefined_ID_DFR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_DFR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CLIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def HACR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HACR ) : SailM HACR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg HACR_EL2) 0 32)))

def HACR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HACR_Type := value_name
  writeReg HACR_EL2 (Sail.BitVec.updateSubrange (← readReg HACR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HACR r

def undefined_ICV_IGRPEN1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_CTR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_PMUSERENR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_CNTHPS_CTL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGBVR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGBVR_Type := value_name
  writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg DBGBVR_EL1) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _DBGBVR (vectorUpdate (← readReg _DBGBVR) n r)

def undefined_PMCEID1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def PMCEID1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMCEID1 ) : SailM PMCEID1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg PMCEID1_EL0) 0 32)))

def undefined_DBGAUTHSTATUS_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICC_IAR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def PMCNTENSET_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCNTENSET_Type := value_name
  writeReg PMCNTENSET_EL0 (Sail.BitVec.updateSubrange (← readReg PMCNTENSET_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _PMCNTENSET r

def undefined_ICV_IGRPEN0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ID_MMFR3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_MMFR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMCEID0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def PMCEID0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMCEID0 ) : SailM PMCEID0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg PMCEID0_EL0) 0 32)))

def undefined_ICV_CTLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGBXVR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGBXVR_Type := value_name
  writeReg DBGBVR_EL1 (vectorUpdate (← readReg DBGBVR_EL1) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg DBGBVR_EL1) n) 63 32 (BitVec.slice r 0 32)))
  writeReg _DBGBXVR (vectorUpdate (← readReg _DBGBXVR) n r)

def undefined_ID_ISAR6_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def HACTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HACTLR ) : SailM HACTLR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ACTLR_EL2) 0 32)))

def HACTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HACTLR_Type := value_name
  writeReg ACTLR_EL2 (Sail.BitVec.updateSubrange (← readReg ACTLR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HACTLR r

def undefined_DBGCLAIMCLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGWVR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGWVR_Type := value_name
  writeReg DBGWVR_EL1 (vectorUpdate (← readReg DBGWVR_EL1) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg DBGWVR_EL1) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _DBGWVR (vectorUpdate (← readReg _DBGWVR) n r)

def undefined_ICV_HPPIR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ID_MMFR5_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICV_AP0R_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _ICV_AP0R) n)) ) : SailM ICV_AP0R_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg ICV_AP0R_EL1) n) 0 32)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICV_AP0R_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_AP0R_Type := value_name
  writeReg ICV_AP0R_EL1 (vectorUpdate (← readReg ICV_AP0R_EL1) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ICV_AP0R_EL1) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _ICV_AP0R (vectorUpdate (← readReg _ICV_AP0R) n r)

def undefined_HRMR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ID_PFR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def HMAIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HMAIR0_Type := value_name
  writeReg MAIR_EL2 (Sail.BitVec.updateSubrange (← readReg MAIR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HMAIR0 r

def undefined_ICV_EOIR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def DACR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DACR_Type := value_name
  writeReg DACR32_EL2 (Sail.BitVec.updateSubrange (← readReg DACR32_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _DACR_NS r

def undefined_ICH_VTR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGWCR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGWCR_Type := value_name
  writeReg DBGWCR_EL1 (vectorUpdate (← readReg DBGWCR_EL1) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg DBGWCR_EL1) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _DBGWCR (vectorUpdate (← readReg _DBGWCR) n r)

def undefined_ICH_VMCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_DBGDEVID1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGDEVID1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_DBGDEVID1_Type_PCSROffset (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_DBGDEVID1_Type_PCSROffset (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_EDDEVID1_Type_PCSROffset (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_EDDEVID1_Type_PCSROffset (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def undefined_ICV_RPR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ID_ISAR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def PMINTENCLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMINTENCLR_Type := value_name
  writeReg PMINTENCLR_EL1 (Sail.BitVec.updateSubrange (← readReg PMINTENCLR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _PMINTENCLR r

def undefined_ICV_IAR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ID_MMFR4_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_MMFR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_ICC_EOIR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def TPIDRURW_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _TPIDRURW_NS ) : SailM TPIDRURW_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg TPIDR_EL0) 0 32)))

def TPIDRURW_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRURW_Type := value_name
  writeReg TPIDR_EL0 (Sail.BitVec.updateSubrange (← readReg TPIDR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _TPIDRURW_NS r

def undefined_ICC_BPR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICV_AP1R_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _ICV_AP1R) n)) ) : SailM ICV_AP1R_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg ICV_AP1R_EL1) n) 0 32)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICV_AP1R_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_AP1R_Type := value_name
  writeReg ICV_AP1R_EL1 (vectorUpdate (← readReg ICV_AP1R_EL1) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ICV_AP1R_EL1) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _ICV_AP1R (vectorUpdate (← readReg _ICV_AP1R) n r)

def ADFSR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ADFSR_NS ) : SailM ADFSR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AFSR0_EL1) 0 32)))

def ADFSR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ADFSR_Type := value_name
  writeReg AFSR0_EL1 (Sail.BitVec.updateSubrange (← readReg AFSR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ADFSR_NS r

def undefined_CNTHCTL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def _get_CNTHCTL_Type_PL1PCEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_CNTHCTL_Type_PL1PCEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_CNTHCTL_Type_PL1PCTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_CNTHCTL_Type_PL1PCTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def undefined_ICC_EOIR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def REVIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _REVIDR ) : SailM REVIDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg REVIDR_EL1) 0 32)))

def undefined_ID_MMFR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_MMFR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_ICV_BPR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICC_RPR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_MVFR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICC_MSRE_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ICC_MSRE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMMIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMMIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_VMPIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def MAIR0_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR0_Type := value_name
  writeReg PRRR_S (Sail.BitVec.updateSubrange (← readReg PRRR_S) 31 0 (BitVec.slice r 0 32))
  writeReg _MAIR0_S r

def undefined_FPSID_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_FPSID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_FPSID_Type_Subarchitecture (v : (BitVec 32)) : (BitVec 7) :=
  (Sail.BitVec.extractLsb v 22 16)

def _update_FPSID_Type_Subarchitecture (v : (BitVec 32)) (x : (BitVec 7)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 16 x)

def undefined_ICC_MCTLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ICC_MCTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_ICC_DIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_PMSELR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_DBGCLAIMSET_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def TPIDRURO_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _TPIDRURO_NS ) : SailM TPIDRURO_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg TPIDRRO_EL0) 0 32)))

def TPIDRURO_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRURO_Type := value_name
  writeReg TPIDRRO_EL0 (Sail.BitVec.updateSubrange (← readReg TPIDRRO_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _TPIDRURO_NS r

def undefined_ICC_IGRPEN0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_DBGDTRTXext_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGDTRTXext_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_DBGDTRTXext_Type_DTRTX (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_DBGDTRTXext_Type_DTRTX (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_DBGDTRTXint_Type_DTRTX (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_DBGDTRTXint_Type_DTRTX (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def DBGDTRTXext_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGDTRTXext ) : SailM DBGDTRTXext_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg OSDTRTX_EL1) 0 32)))

def DBGDTRTXext_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDTRTXext_Type := value_name
  writeReg OSDTRTX_EL1 (Sail.BitVec.updateSubrange (← readReg OSDTRTX_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGDTRTXext r

def ACTLR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ACTLR_NS ) : SailM ACTLR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ACTLR_EL1) 0 32)))

def ACTLR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ACTLR_Type := value_name
  writeReg ACTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ACTLR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ACTLR_NS r

def undefined_MVFR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_MVFR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_DBGOSLAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGOSLAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_DBGOSLAR_Type_OSLA (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_DBGOSLAR_Type_OSLA (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def undefined_DBGDTRRXext_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGDTRRXext_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_DBGDTRRXext_Type_DTRRX (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_DBGDTRRXext_Type_DTRRX (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_DBGDTRRXint_Type_DTRRX (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_DBGDTRRXint_Type_DTRRX (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def DBGDTRRXext_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGDTRRXext ) : SailM DBGDTRRXext_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg OSDTRRX_EL1) 0 32)))

def DBGDTRRXext_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDTRRXext_Type := value_name
  writeReg OSDTRRX_EL1 (Sail.BitVec.updateSubrange (← readReg OSDTRRX_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGDTRRXext r

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP1R_S_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _ICC_AP1R_S) n)) ) : SailM ICC_AP1R_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg ICC_AP1R_EL1_S) n) 0 32)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP1R_S_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_AP1R_Type := value_name
  writeReg ICC_AP1R_EL1_S (vectorUpdate (← readReg ICC_AP1R_EL1_S) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ICC_AP1R_EL1_S) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _ICC_AP1R_S (vectorUpdate (← readReg _ICC_AP1R_S) n r)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP1R_NS_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _ICC_AP1R_NS) n)) ) : SailM ICC_AP1R_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg ICC_AP1R_EL1_NS) n) 0 32)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP1R_NS_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_AP1R_Type := value_name
  writeReg ICC_AP1R_EL1_NS (vectorUpdate (← readReg ICC_AP1R_EL1_NS) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ICC_AP1R_EL1_NS) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _ICC_AP1R_NS (vectorUpdate (← readReg _ICC_AP1R_NS) n r)

def undefined_CNTHVS_CTL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICH_AP1R_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ICH_AP1R_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICH_AP1R_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _ICH_AP1R) n)) ) : SailM ICH_AP1R_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg ICH_AP1R_EL2) n) 0 32)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICH_AP1R_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_AP1R_Type := value_name
  writeReg ICH_AP1R_EL2 (vectorUpdate (← readReg ICH_AP1R_EL2) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ICH_AP1R_EL2) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _ICH_AP1R (vectorUpdate (← readReg _ICH_AP1R) n r)

def undefined_ID_MMFR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_MMFR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_ICV_BPR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICH_EISR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def AMAIR0_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMAIR0_NS ) : SailM AMAIR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMAIR_EL1) 0 32)))

def AMAIR0_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMAIR0_Type := value_name
  writeReg AMAIR_EL1 (Sail.BitVec.updateSubrange (← readReg AMAIR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _AMAIR0_NS r

def undefined_MVFR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_MVFR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def HAMAIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HAMAIR0 ) : SailM HAMAIR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMAIR_EL2) 0 32)))

def HAMAIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HAMAIR0_Type := value_name
  writeReg AMAIR_EL2 (Sail.BitVec.updateSubrange (← readReg AMAIR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HAMAIR0 r

def undefined_ICC_HSRE_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICH_AP0R_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ICH_AP0R_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICH_AP0R_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _ICH_AP0R) n)) ) : SailM ICH_AP0R_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg ICH_AP0R_EL2) n) 0 32)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICH_AP0R_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_AP0R_Type := value_name
  writeReg ICH_AP0R_EL2 (vectorUpdate (← readReg ICH_AP0R_EL2) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ICH_AP0R_EL2) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _ICH_AP0R (vectorUpdate (← readReg _ICH_AP0R) n r)

def undefined_ID_ISAR5_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def AIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AIDR ) : SailM AIDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AIDR_EL1) 0 32)))

def undefined_ICC_PMR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICV_EOIR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ID_PFR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_PFR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_ICH_HCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_RMR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def HMAIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HMAIR1_Type := value_name
  writeReg MAIR_EL2 (Sail.BitVec.updateSubrange (← readReg MAIR_EL2) 63 32 (BitVec.slice r 0 32))
  writeReg _HMAIR1 r

def undefined_PMCEID3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def PMCEID3_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMCEID3 ) : SailM PMCEID3_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg PMCEID1_EL0) 32 32)))

def undefined_ICC_HPPIR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ID_ISAR4_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_ISAR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMCEID2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def PMCEID2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMCEID2 ) : SailM PMCEID2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg PMCEID0_EL0) 32 32)))

def HSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HSR ) : SailM HSR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ESR_EL2) 0 32)))

def undefined_ID_DFR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICH_LR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ICH_LR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def ICH_LR_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _ICH_LR) n)) ) : SailM ICH_LR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg ICH_LR_EL2) n) 0 32)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def ICH_LR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_LR_Type := value_name
  writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ICH_LR_EL2) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _ICH_LR (vectorUpdate (← readReg _ICH_LR) n r)

def HADFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HADFSR ) : SailM HADFSR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AFSR0_EL2) 0 32)))

def HADFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HADFSR_Type := value_name
  writeReg AFSR0_EL2 (Sail.BitVec.updateSubrange (← readReg AFSR0_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HADFSR r

def undefined_ICV_PMR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICV_HPPIR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGBCR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGBCR_Type := value_name
  writeReg DBGBCR_EL1 (vectorUpdate (← readReg DBGBCR_EL1) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg DBGBCR_EL1) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _DBGBCR (vectorUpdate (← readReg _DBGBCR) n r)

def undefined_ID_ISAR3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_ISAR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_ICC_MGRPEN1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ICC_MGRPEN1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_TLBTR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_TLBTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_TLBTR_Type_nU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_TLBTR_Type_nU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def CNTFRQ_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTFRQ ) : SailM CNTFRQ_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CNTFRQ_EL0) 0 32)))

def CNTFRQ_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTFRQ_Type := value_name
  writeReg CNTFRQ_EL0 (Sail.BitVec.updateSubrange (← readReg CNTFRQ_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _CNTFRQ r

def undefined_PMINTENSET_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMINTENSET_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def PMINTENSET_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMINTENSET ) : SailM PMINTENSET_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg PMINTENSET_EL1) 0 32)))

def PMINTENSET_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMINTENSET_Type := value_name
  writeReg PMINTENSET_EL1 (Sail.BitVec.updateSubrange (← readReg PMINTENSET_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _PMINTENSET r

def undefined_DBGDEVID_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGDEVID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_DBGDEVID_Type_AuxRegs (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_DBGDEVID_Type_AuxRegs (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_EDDEVID_Type_AuxRegs (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_EDDEVID_Type_AuxRegs (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_DBGDEVID_Type_BPAddrMask (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_DBGDEVID_Type_BPAddrMask (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_DBGDEVID_Type_CIDMask (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_DBGDEVID_Type_CIDMask (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_DBGDEVID_Type_VectorCatch (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_DBGDEVID_Type_VectorCatch (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_DBGDEVID_Type_VirtExtns (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_DBGDEVID_Type_VirtExtns (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_DBGDEVID_Type_WPAddrMask (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_DBGDEVID_Type_WPAddrMask (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def undefined_DBGOSECCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGOSECCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def DBGOSECCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGOSECCR ) : SailM DBGOSECCR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg OSECCR_EL1) 0 32)))

def DBGOSECCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGOSECCR_Type := value_name
  writeReg OSECCR_EL1 (Sail.BitVec.updateSubrange (← readReg OSECCR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGOSECCR r

def undefined_CCSIDR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_CNTHV_CTL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICH_MISR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def ACTLR2_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ACTLR2_NS ) : SailM ACTLR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ACTLR_EL1) 32 32)))

def ACTLR2_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ACTLR2_Type := value_name
  writeReg ACTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ACTLR_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _ACTLR2_NS r

def undefined_ICV_IAR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ID_MMFR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_MMFR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def HAMAIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HAMAIR1 ) : SailM HAMAIR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMAIR_EL2) 32 32)))

def HAMAIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HAMAIR1_Type := value_name
  writeReg AMAIR_EL2 (Sail.BitVec.updateSubrange (← readReg AMAIR_EL2) 63 32 (BitVec.slice r 0 32))
  writeReg _HAMAIR1 r

def undefined_ISR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def HAIFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HAIFSR ) : SailM HAIFSR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AFSR1_EL2) 0 32)))

def HAIFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HAIFSR_Type := value_name
  writeReg AFSR1_EL2 (Sail.BitVec.updateSubrange (← readReg AFSR1_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HAIFSR r

def undefined_ID_PFR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_PFR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def ELR_hyp_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ELR_hyp ) : SailM ELR_hyp_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ELR_EL2) 0 32)))

def undefined_MIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_MIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP0R_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _ICC_AP0R) n)) ) : SailM ICC_AP0R_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg ICC_AP0R_EL1) n) 0 32)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP0R_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_AP0R_Type := value_name
  writeReg ICC_AP0R_EL1 (vectorUpdate (← readReg ICC_AP0R_EL1) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ICC_AP0R_EL1) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _ICC_AP0R (vectorUpdate (← readReg _ICC_AP0R) n r)

def undefined_DBGDIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGDIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_DBGDIDR_Type_SE_imp (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_DBGDIDR_Type_SE_imp (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_DBGDIDR_Type_Version (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_DBGDIDR_Type_Version (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_DBGDIDR_Type_nSUHD_imp (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_DBGDIDR_Type_nSUHD_imp (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def __set_CNTP_CTL_S (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTP_CTL_Type := value_name
  writeReg CNTP_CTL_S (Sail.BitVec.updateSubrange (← readReg CNTP_CTL_S) 1 0 (BitVec.slice r 0 2))
  writeReg CNTP_CTL_S (Sail.BitVec.updateSubrange (← readReg CNTP_CTL_S) 31 3 (BitVec.slice r 3 29))

def TPIDRPRW_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _TPIDRPRW_NS ) : SailM TPIDRPRW_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg TPIDR_EL1) 0 32)))

def TPIDRPRW_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRPRW_Type := value_name
  writeReg TPIDR_EL1 (Sail.BitVec.updateSubrange (← readReg TPIDR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _TPIDRPRW_NS r

def IFAR_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _IFAR_S ) : SailM IFAR_Type )
  if ((HaveEL EL2) : Bool)
  then (do (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg FAR_EL2) 32 32))))
  else (do (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← (HIFAR_read ())) 0 32))))

def IFAR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _IFAR_NS ) : SailM IFAR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg FAR_EL1) 32 32)))

def undefined_DBGDTRRXint_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGDTRRXint_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def DBGDTRRXint_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGDTRRXint ) : SailM DBGDTRRXint_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DBGDTRRX_EL0) 0 32)))

def undefined_VPIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_VPIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMSWINC_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 31 -/
def PMEVTYPER_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMEVTYPER_Type := value_name
  writeReg PMEVTYPER_EL0 (vectorUpdate (← readReg PMEVTYPER_EL0) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg PMEVTYPER_EL0) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _PMEVTYPER (vectorUpdate (← readReg _PMEVTYPER) n r)

def undefined_CNTV_CTL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def HTPIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HTPIDR ) : SailM HTPIDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg TPIDR_EL2) 0 32)))

def HTPIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HTPIDR_Type := value_name
  writeReg TPIDR_EL2 (Sail.BitVec.updateSubrange (← readReg TPIDR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HTPIDR r

def CONTEXTIDR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CONTEXTIDR_Type := value_name
  writeReg CONTEXTIDR_EL1 (Sail.BitVec.updateSubrange (← readReg CONTEXTIDR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _CONTEXTIDR_NS r

def DFAR_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DFAR_S ) : SailM DFAR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← (HDFAR_read ())) 0 32)))

def DFAR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DFAR_NS ) : SailM DFAR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg FAR_EL1) 0 32)))

def PMCNTENCLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCNTENCLR_Type := value_name
  writeReg PMCNTENCLR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCNTENCLR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _PMCNTENCLR r

def undefined_ID_ISAR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_ISAR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_DBGDTRTXint_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGDTRTXint_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def DBGDTRTXint_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDTRTXint_Type := value_name
  writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRTX_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGDTRTXint r

def AMAIR1_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMAIR1_NS ) : SailM AMAIR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMAIR_EL1) 32 32)))

def AMAIR1_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMAIR1_Type := value_name
  writeReg AMAIR_EL1 (Sail.BitVec.updateSubrange (← readReg AMAIR_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _AMAIR1_NS r

def undefined_CCSIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICV_DIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_MPIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ICH_LRC_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ICH_LRC_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def ICH_LRC_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _ICH_LRC) n)) ) : SailM ICH_LRC_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg ICH_LR_EL2) n) 32 32)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def ICH_LRC_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_LRC_Type := value_name
  writeReg ICH_LR_EL2 (vectorUpdate (← readReg ICH_LR_EL2) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ICH_LR_EL2) n) 63 32 (BitVec.slice r 0 32)))
  writeReg _ICH_LRC (vectorUpdate (← readReg _ICH_LRC) n r)

def MAIR1_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR1_Type := value_name
  writeReg NMRR_S (Sail.BitVec.updateSubrange (← readReg NMRR_S) 31 0 (BitVec.slice r 0 32))
  writeReg _MAIR1_S r

def undefined_ICC_HPPIR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ID_ISAR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_ID_ISAR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMEVTYPER0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMEVTYPER0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def AMEVTYPER0_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _AMEVTYPER0) n)) ) : SailM AMEVTYPER0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) n) 0 32)))

def undefined_AMUSERENR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_AMEVTYPER1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMEVTYPER1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def AMEVTYPER1_read (n : Nat) : SailM (BitVec 32) := do
  let r ← (( do (pure (GetElem?.getElem! (← readReg _AMEVTYPER1) n)) ) : SailM AMEVTYPER1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) n) 0 32)))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def AMEVTYPER1_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMEVTYPER1_Type := value_name
  writeReg AMEVTYPER1_EL0 (vectorUpdate (← readReg AMEVTYPER1_EL0) n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg AMEVTYPER1_EL0) n) 31 0 (BitVec.slice r 0 32)))
  writeReg _AMEVTYPER1 (vectorUpdate (← readReg _AMEVTYPER1) n r)

def undefined_AMCGCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_AMCFGR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_AMCNTENCLR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_AMCNTENSET0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_AMCNTENCLR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_AMCNTENSET1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_AMCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_ERRIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def ERXFR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXFR2 ) : SailM ERXFR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXFR_EL1) 32 32)))

def ERXMISC2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC2 ) : SailM ERXMISC2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXMISC1_EL1) 0 32)))

def ERXMISC2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC2_Type := value_name
  writeReg ERXMISC1_EL1 (Sail.BitVec.updateSubrange (← readReg ERXMISC1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ERXMISC2 r

def ERXFR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXFR ) : SailM ERXFR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXFR_EL1) 0 32)))

def ERXADDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXADDR ) : SailM ERXADDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXADDR_EL1) 0 32)))

def ERXADDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXADDR_Type := value_name
  writeReg ERXADDR_EL1 (Sail.BitVec.updateSubrange (← readReg ERXADDR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ERXADDR r

def ERXMISC0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC0 ) : SailM ERXMISC0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXMISC0_EL1) 0 32)))

def ERXMISC0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC0_Type := value_name
  writeReg ERXMISC0_EL1 (Sail.BitVec.updateSubrange (← readReg ERXMISC0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ERXMISC0 r

def ERXMISC5_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC5 ) : SailM ERXMISC5_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXMISC2_EL1) 32 32)))

def ERXMISC5_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC5_Type := value_name
  writeReg ERXMISC2_EL1 (Sail.BitVec.updateSubrange (← readReg ERXMISC2_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _ERXMISC5 r

def undefined_ERRSELR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def ERXCTLR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXCTLR2 ) : SailM ERXCTLR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXCTLR_EL1) 32 32)))

def ERXCTLR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXCTLR2_Type := value_name
  writeReg ERXCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ERXCTLR_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _ERXCTLR2 r

def ERXMISC1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC1 ) : SailM ERXMISC1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXMISC0_EL1) 32 32)))

def ERXMISC1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC1_Type := value_name
  writeReg ERXMISC0_EL1 (Sail.BitVec.updateSubrange (← readReg ERXMISC0_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _ERXMISC1 r

def ERXCTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXCTLR ) : SailM ERXCTLR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXCTLR_EL1) 0 32)))

def ERXCTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXCTLR_Type := value_name
  writeReg ERXCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ERXCTLR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ERXCTLR r

def ERXMISC6_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC6 ) : SailM ERXMISC6_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXMISC3_EL1) 0 32)))

def ERXMISC6_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC6_Type := value_name
  writeReg ERXMISC3_EL1 (Sail.BitVec.updateSubrange (← readReg ERXMISC3_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ERXMISC6 r

def ERXMISC4_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC4 ) : SailM ERXMISC4_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXMISC2_EL1) 0 32)))

def ERXMISC4_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC4_Type := value_name
  writeReg ERXMISC2_EL1 (Sail.BitVec.updateSubrange (← readReg ERXMISC2_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ERXMISC4 r

def ERXADDR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXADDR2 ) : SailM ERXADDR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXADDR_EL1) 32 32)))

def ERXADDR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXADDR2_Type := value_name
  writeReg ERXADDR_EL1 (Sail.BitVec.updateSubrange (← readReg ERXADDR_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _ERXADDR2 r

def ERXMISC7_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC7 ) : SailM ERXMISC7_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXMISC3_EL1) 32 32)))

def ERXMISC7_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC7_Type := value_name
  writeReg ERXMISC3_EL1 (Sail.BitVec.updateSubrange (← readReg ERXMISC3_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _ERXMISC7 r

def ERXMISC3_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC3 ) : SailM ERXMISC3_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXMISC1_EL1) 32 32)))

def ERXMISC3_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC3_Type := value_name
  writeReg ERXMISC1_EL1 (Sail.BitVec.updateSubrange (← readReg ERXMISC1_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _ERXMISC3 r

def ERXSTATUS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXSTATUS ) : SailM ERXSTATUS_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERXSTATUS_EL1) 0 32)))

def ERXSTATUS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXSTATUS_Type := value_name
  writeReg ERXSTATUS_EL1 (Sail.BitVec.updateSubrange (← readReg ERXSTATUS_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ERXSTATUS r

def undefined_GICD_CTLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICD_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICD_CTLR_Type_ARE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_GICD_CTLR_Type_ARE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_GICD_CTLR_Type_ARE_S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_GICD_CTLR_Type_ARE_S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_GICD_CTLR_Type_E1NWF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_GICD_CTLR_Type_E1NWF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_GICD_CTLR_Type_EnableGrp0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_GICD_CTLR_Type_EnableGrp0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICC_CTLR_Type_EnableGrp0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICV_CTLR_Type_EnableGrp0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICC_CTLR_Type_EnableGrp0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_GICV_CTLR_Type_EnableGrp0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_GICD_CTLR_Type_EnableGrp1A (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_GICD_CTLR_Type_EnableGrp1A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GICD_CTLR_Type_RWP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_GICD_CTLR_Type_RWP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_GICR_CTLR_Type_RWP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_GICR_CTLR_Type_RWP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_GICD_CTLR_Type_nASSGIreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_GICD_CTLR_Type_nASSGIreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def undefined_GICC_IAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_IAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CTILAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTILAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTILAR_Type_KEY (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_CTILAR_Type_KEY (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_EDLAR_Type_KEY (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_PMLAR_Type_KEY (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_EDLAR_Type_KEY (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_PMLAR_Type_KEY (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def undefined_CTIPIDR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIPIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTIPIDR2_Type_DES_1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _update_CTIPIDR2_Type_DES_1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_AMPIDR2_Type_DES_1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_EDPIDR2_Type_DES_1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_PMPIDR2_Type_DES_1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _get_AMPIDR2_Type_DES_1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_EDPIDR2_Type_DES_1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_PMPIDR2_Type_DES_1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_CTIPIDR2_Type_JEDEC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_CTIPIDR2_Type_JEDEC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_AMPIDR2_Type_JEDEC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_EDPIDR2_Type_JEDEC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMPIDR2_Type_JEDEC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_AMPIDR2_Type_JEDEC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_EDPIDR2_Type_JEDEC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMPIDR2_Type_JEDEC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_CTIPIDR2_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_CTIPIDR2_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_AMDEVARCH_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_AMPIDR2_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_CTIDEVARCH_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_EDDEVARCH_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_EDPIDR2_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PMPIDR2_Type_REVISION (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_AMDEVARCH_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_AMPIDR2_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_CTIDEVARCH_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_EDDEVARCH_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_EDPIDR2_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_PMPIDR2_Type_REVISION (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def undefined_CTICIDR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTICIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTICIDR1_Type_CLASS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_CTICIDR1_Type_CLASS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_AMCIDR1_Type_CLASS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_EDCIDR1_Type_CLASS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PMCIDR1_Type_CLASS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_AMCIDR1_Type_CLASS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_EDCIDR1_Type_CLASS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_PMCIDR1_Type_CLASS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_CTICIDR1_Type_PRMBL_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_CTICIDR1_Type_PRMBL_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_AMCIDR1_Type_PRMBL_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_EDCIDR1_Type_PRMBL_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PMCIDR1_Type_PRMBL_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_AMCIDR1_Type_PRMBL_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_EDCIDR1_Type_PRMBL_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PMCIDR1_Type_PRMBL_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def undefined_GICH_MISR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICH_MISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CTIDEVTYPE_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIDEVTYPE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTIDEVTYPE_Type_MAJOR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_CTIDEVTYPE_Type_MAJOR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_AMDEVTYPE_Type_MAJOR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_EDDEVTYPE_Type_MAJOR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PMDEVTYPE_Type_MAJOR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_AMDEVTYPE_Type_MAJOR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_EDDEVTYPE_Type_MAJOR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PMDEVTYPE_Type_MAJOR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_CTIDEVTYPE_Type_SUB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_CTIDEVTYPE_Type_SUB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_AMDEVTYPE_Type_SUB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_EDDEVTYPE_Type_SUB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PMDEVTYPE_Type_SUB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_AMDEVTYPE_Type_SUB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_EDDEVTYPE_Type_SUB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_PMDEVTYPE_Type_SUB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def undefined_GITS_CTLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GITS_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GITS_CTLR_Type_Enabled (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_GITS_CTLR_Type_Enabled (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GITS_CTLR_Type_ITS_Number (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_GITS_CTLR_Type_ITS_Number (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_GITS_CTLR_Type_ImDe (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_GITS_CTLR_Type_ImDe (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GITS_CTLR_Type_Quiescent (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_GITS_CTLR_Type_Quiescent (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def undefined_GICR_IIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_IIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDDEVARCH_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDDEVARCH_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDDEVARCH_Type_ARCHITECT (v : (BitVec 32)) : (BitVec 11) :=
  (Sail.BitVec.extractLsb v 31 21)

def _update_EDDEVARCH_Type_ARCHITECT (v : (BitVec 32)) (x : (BitVec 11)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 21 x)

def _update_AMDEVARCH_Type_ARCHITECT (v : (BitVec 32)) (x : (BitVec 11)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 21 x)

def _update_CTIDEVARCH_Type_ARCHITECT (v : (BitVec 32)) (x : (BitVec 11)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 21 x)

def _get_AMDEVARCH_Type_ARCHITECT (v : (BitVec 32)) : (BitVec 11) :=
  (Sail.BitVec.extractLsb v 31 21)

def _get_CTIDEVARCH_Type_ARCHITECT (v : (BitVec 32)) : (BitVec 11) :=
  (Sail.BitVec.extractLsb v 31 21)

def _get_EDDEVARCH_Type_ARCHPART (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 11 0)

def _update_EDDEVARCH_Type_ARCHPART (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 0 x)

def _get_EDDEVARCH_Type_ARCHVER (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_EDDEVARCH_Type_ARCHVER (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_EDDEVARCH_Type_PRESENT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_EDDEVARCH_Type_PRESENT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_AMDEVARCH_Type_PRESENT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_CTIDEVARCH_Type_PRESENT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_AMDEVARCH_Type_PRESENT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_CTIDEVARCH_Type_PRESENT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def undefined_CTIPIDR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIPIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTIPIDR1_Type_DES_0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_CTIPIDR1_Type_DES_0 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_AMPIDR1_Type_DES_0 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_EDPIDR1_Type_DES_0 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PMPIDR1_Type_DES_0 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_AMPIDR1_Type_DES_0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_EDPIDR1_Type_DES_0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_PMPIDR1_Type_DES_0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_CTIPIDR1_Type_PART_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_CTIPIDR1_Type_PART_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_AMPIDR1_Type_PART_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_EDPIDR1_Type_PART_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PMPIDR1_Type_PART_1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_AMPIDR1_Type_PART_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_EDPIDR1_Type_PART_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PMPIDR1_Type_PART_1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def undefined_GICV_IAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_IAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CNTSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CNTSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CNTSR_Type_DBGH (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_CNTSR_Type_DBGH (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_CNTSR_Type_FCACK (v : (BitVec 32)) : (BitVec 10) :=
  (Sail.BitVec.extractLsb v 17 8)

def _update_CNTSR_Type_FCACK (v : (BitVec 32)) (x : (BitVec 10)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 8 x)

def undefined_EDCIDR3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDCIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDCIDR3_Type_PRMBL_3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_EDCIDR3_Type_PRMBL_3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_AMCIDR3_Type_PRMBL_3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_CTICIDR3_Type_PRMBL_3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_PMCIDR3_Type_PRMBL_3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_AMCIDR3_Type_PRMBL_3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_CTICIDR3_Type_PRMBL_3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_PMCIDR3_Type_PRMBL_3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def undefined_GICM_SETSPI_NSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICM_SETSPI_NSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICR_WAKER_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_WAKER_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICR_WAKER_Type_ChildrenAsleep (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_GICR_WAKER_Type_ChildrenAsleep (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GICR_WAKER_Type_ProcessorSleep (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_GICR_WAKER_Type_ProcessorSleep (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def undefined_GITS_PARTIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GITS_PARTIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GITS_PARTIDR_Type_PARTID (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_GITS_PARTIDR_Type_PARTID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_GICR_PARTIDR_Type_PARTID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_GICR_PARTIDR_Type_PARTID (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_GITS_PARTIDR_Type_PMG (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _update_GITS_PARTIDR_Type_PMG (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_GICR_PARTIDR_Type_PMG (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _get_GICR_PARTIDR_Type_PMG (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def undefined_GICV_HPPIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_HPPIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CTIPIDR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIPIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTIPIDR0_Type_PART_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_CTIPIDR0_Type_PART_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_AMPIDR0_Type_PART_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_EDPIDR0_Type_PART_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_PMPIDR0_Type_PART_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_AMPIDR0_Type_PART_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_EDPIDR0_Type_PART_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_PMPIDR0_Type_PART_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def undefined_GICM_SETSPI_SR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICM_SETSPI_SR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICV_DIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_DIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDPIDR3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDPIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDPIDR3_Type_CMOD (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_EDPIDR3_Type_CMOD (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


