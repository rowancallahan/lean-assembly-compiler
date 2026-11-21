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
import Armv9.V8Base.P00
import Armv9.V8Base.P01

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

def _update_AMPIDR3_Type_CMOD (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_CTIPIDR3_Type_CMOD (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PMPIDR3_Type_CMOD (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_AMPIDR3_Type_CMOD (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_CTIPIDR3_Type_CMOD (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PMPIDR3_Type_CMOD (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_EDPIDR3_Type_REVAND (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_EDPIDR3_Type_REVAND (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_AMPIDR3_Type_REVAND (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_CTIPIDR3_Type_REVAND (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PMPIDR3_Type_REVAND (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_AMPIDR3_Type_REVAND (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_CTIPIDR3_Type_REVAND (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_PMPIDR3_Type_REVAND (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def undefined_GICC_STATUSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_STATUSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICC_STATUSR_Type_ASV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_GICC_STATUSR_Type_ASV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_GICC_STATUSR_Type_RRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_GICC_STATUSR_Type_RRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICD_STATUSR_Type_RRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICR_STATUSR_Type_RRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GICV_STATUSR_Type_RRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GITS_STATUSR_Type_RRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICD_STATUSR_Type_RRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_GICR_STATUSR_Type_RRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_GICV_STATUSR_Type_RRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_GITS_STATUSR_Type_RRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_GICC_STATUSR_Type_RWOD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_GICC_STATUSR_Type_RWOD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_GICD_STATUSR_Type_RWOD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_GICR_STATUSR_Type_RWOD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_GICV_STATUSR_Type_RWOD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_GITS_STATUSR_Type_RWOD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GICD_STATUSR_Type_RWOD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_GICR_STATUSR_Type_RWOD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_GICV_STATUSR_Type_RWOD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_GITS_STATUSR_Type_RWOD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_GICC_STATUSR_Type_WRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_GICC_STATUSR_Type_WRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GICD_STATUSR_Type_WRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GICR_STATUSR_Type_WRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GICV_STATUSR_Type_WRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GITS_STATUSR_Type_WRD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GICD_STATUSR_Type_WRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_GICR_STATUSR_Type_WRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_GICV_STATUSR_Type_WRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_GITS_STATUSR_Type_WRD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_GICC_STATUSR_Type_WROD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_GICC_STATUSR_Type_WROD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GICD_STATUSR_Type_WROD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GICR_STATUSR_Type_WROD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GICV_STATUSR_Type_WROD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GITS_STATUSR_Type_WROD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_GICD_STATUSR_Type_WROD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_GICR_STATUSR_Type_WROD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_GICV_STATUSR_Type_WROD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_GITS_STATUSR_Type_WROD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def undefined_GICM_IIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICM_IIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICR_VSGIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_VSGIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDDEVTYPE_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDDEVTYPE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICM_TYPER_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICM_TYPER_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICM_TYPER_Type_CLR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_GICM_TYPER_Type_CLR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_GICM_TYPER_Type_NumSPIs (v : (BitVec 32)) : (BitVec 11) :=
  (Sail.BitVec.extractLsb v 10 0)

def _update_GICM_TYPER_Type_NumSPIs (v : (BitVec 32)) (x : (BitVec 11)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 0 x)

def undefined_GICD_TYPER2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICD_TYPER2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICD_TYPER2_Type_VID (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _update_GICD_TYPER2_Type_VID (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _get_GICD_TYPER2_Type_VIL (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_GICD_TYPER2_Type_VIL (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_GICD_TYPER2_Type_nASSGIcap (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_GICD_TYPER2_Type_nASSGIcap (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def undefined_GICH_EISR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICH_EISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICH_ELRSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICH_ELRSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICM_CLRSPI_NSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICM_CLRSPI_NSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICV_STATUSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_STATUSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDPIDR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDPIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICM_CLRSPI_SR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICM_CLRSPI_SR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICV_AEOIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_AEOIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICC_PMR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_PMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICV_ABPR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_ABPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICV_ABPR_Type_Binary_Point (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _update_GICV_ABPR_Type_Binary_Point (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_GICC_ABPR_Type_Binary_Point (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_GICC_BPR_Type_Binary_Point (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_GICV_BPR_Type_Binary_Point (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _get_GICC_ABPR_Type_Binary_Point (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_GICC_BPR_Type_Binary_Point (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_GICV_BPR_Type_Binary_Point (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def undefined_CTIDEVARCH_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIDEVARCH_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTIDEVARCH_Type_ARCHID (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_CTIDEVARCH_Type_ARCHID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_AMDEVARCH_Type_ARCHID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_AMDEVARCH_Type_ARCHID (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def undefined_GICR_MPAMIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_MPAMIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICR_MPAMIDR_Type_PARTIDmax (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_GICR_MPAMIDR_Type_PARTIDmax (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_GITS_MPAMIDR_Type_PARTIDmax (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_GITS_MPAMIDR_Type_PARTIDmax (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_GICR_MPAMIDR_Type_PMGmax (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _update_GICR_MPAMIDR_Type_PMGmax (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_GITS_MPAMIDR_Type_PMGmax (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _get_GITS_MPAMIDR_Type_PMGmax (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def undefined_CTICIDR3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTICIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICC_RPR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_RPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICV_AIAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_AIAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICV_RPR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_RPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICV_AHPPIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_AHPPIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICR_CTLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICR_CTLR_Type_CES (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_GICR_CTLR_Type_CES (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GICR_CTLR_Type_DPG0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_GICR_CTLR_Type_DPG0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_GICR_CTLR_Type_DPG1NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_GICR_CTLR_Type_DPG1NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_GICR_CTLR_Type_DPG1S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_GICR_CTLR_Type_DPG1S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_GICR_CTLR_Type_EnableLPIs (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_GICR_CTLR_Type_EnableLPIs (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICR_CTLR_Type_UWP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_GICR_CTLR_Type_UWP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def undefined_CNTEL0ACR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CNTEL0ACR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICV_BPR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_BPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICV_EOIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_EOIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CNTFID0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def _get_CNTFID0_Type_Frequency (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_CNTFID0_Type_Frequency (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def undefined_GICD_TYPER_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICD_TYPER_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICD_TYPER_Type_CPUNumber (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 7 5)

def _update_GICD_TYPER_Type_CPUNumber (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 5 x)

def _get_GICD_TYPER_Type_DVIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_GICD_TYPER_Type_DVIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_GICD_TYPER_Type_ESPI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_GICD_TYPER_Type_ESPI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_GICD_TYPER_Type_ESPI_range (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 31 27)

def _update_GICD_TYPER_Type_ESPI_range (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 27 x)

def _get_GICD_TYPER_Type_ITLinesNumber (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _update_GICD_TYPER_Type_ITLinesNumber (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _get_GICD_TYPER_Type_LPIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_GICD_TYPER_Type_LPIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_GICD_TYPER_Type_MBIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_GICD_TYPER_Type_MBIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_GICD_TYPER_Type_No1N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_GICD_TYPER_Type_No1N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_GICD_TYPER_Type_SecurityExtn (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_GICD_TYPER_Type_SecurityExtn (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_GICD_TYPER_Type_num_LPIs (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 15 11)

def _update_GICD_TYPER_Type_num_LPIs (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 11 x)

def undefined_CTICIDR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTICIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTICIDR0_Type_PRMBL_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_CTICIDR0_Type_PRMBL_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_AMCIDR0_Type_PRMBL_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_EDCIDR0_Type_PRMBL_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_PMCIDR0_Type_PRMBL_0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_AMCIDR0_Type_PRMBL_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_EDCIDR0_Type_PRMBL_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_PMCIDR0_Type_PRMBL_0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def undefined_GICC_HPPIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_HPPIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICD_CLRSPI_NSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICD_CLRSPI_NSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CTIITCTRL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIITCTRL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTIITCTRL_Type_IME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_CTIITCTRL_Type_IME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_EDITCTRL_Type_IME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMITCTRL_Type_IME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_EDITCTRL_Type_IME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMITCTRL_Type_IME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def undefined_GITS_STATUSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GITS_STATUSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GITS_STATUSR_Type_Overflow (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_GITS_STATUSR_Type_Overflow (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_GITS_STATUSR_Type_Syndrome (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 9 6)

def _update_GITS_STATUSR_Type_Syndrome (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 6 x)

def undefined_GICH_VTR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICH_VTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CTIPIDR3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIPIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICC_CTLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICC_CTLR_Type_EOImodeS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_GICC_CTLR_Type_EOImodeS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_GICC_CTLR_Type_FIQBypDisGrp0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_GICC_CTLR_Type_FIQBypDisGrp0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_GICC_CTLR_Type_FIQEn (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_GICC_CTLR_Type_FIQEn (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GICV_CTLR_Type_FIQEn (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_GICV_CTLR_Type_FIQEn (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_GICC_CTLR_Type_IRQBypDisGrp0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_GICC_CTLR_Type_IRQBypDisGrp0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def undefined_EDPIDR4_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDPIDR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDPIDR4_Type_DES_2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_EDPIDR4_Type_DES_2 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_AMPIDR4_Type_DES_2 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_CTIPIDR4_Type_DES_2 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PMPIDR4_Type_DES_2 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_AMPIDR4_Type_DES_2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_CTIPIDR4_Type_DES_2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PMPIDR4_Type_DES_2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def undefined_CTICONTROL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTICONTROL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTICONTROL_Type_GLBEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_CTICONTROL_Type_GLBEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def undefined_GICR_INMIR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_INMIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICR_INMIR0_Type_nmi0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_GICR_INMIR0_Type_nmi0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICR_INMIR0_Type_nmi1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_GICR_INMIR0_Type_nmi1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GICR_INMIR0_Type_nmi10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_GICR_INMIR0_Type_nmi10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_GICR_INMIR0_Type_nmi11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_GICR_INMIR0_Type_nmi11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_GICR_INMIR0_Type_nmi12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_GICR_INMIR0_Type_nmi12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_GICR_INMIR0_Type_nmi13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_GICR_INMIR0_Type_nmi13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_GICR_INMIR0_Type_nmi14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_GICR_INMIR0_Type_nmi14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_GICR_INMIR0_Type_nmi15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_GICR_INMIR0_Type_nmi15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_GICR_INMIR0_Type_nmi16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_GICR_INMIR0_Type_nmi16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_GICR_INMIR0_Type_nmi17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_GICR_INMIR0_Type_nmi17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_GICR_INMIR0_Type_nmi18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_GICR_INMIR0_Type_nmi18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_GICR_INMIR0_Type_nmi19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_GICR_INMIR0_Type_nmi19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_GICR_INMIR0_Type_nmi2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_GICR_INMIR0_Type_nmi2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GICR_INMIR0_Type_nmi20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_GICR_INMIR0_Type_nmi20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_GICR_INMIR0_Type_nmi21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_GICR_INMIR0_Type_nmi21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_GICR_INMIR0_Type_nmi22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_GICR_INMIR0_Type_nmi22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_GICR_INMIR0_Type_nmi23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_GICR_INMIR0_Type_nmi23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_GICR_INMIR0_Type_nmi24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_GICR_INMIR0_Type_nmi24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_GICR_INMIR0_Type_nmi25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_GICR_INMIR0_Type_nmi25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_GICR_INMIR0_Type_nmi26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_GICR_INMIR0_Type_nmi26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_GICR_INMIR0_Type_nmi27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_GICR_INMIR0_Type_nmi27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_GICR_INMIR0_Type_nmi28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_GICR_INMIR0_Type_nmi28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_GICR_INMIR0_Type_nmi29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_GICR_INMIR0_Type_nmi29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_GICR_INMIR0_Type_nmi3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_GICR_INMIR0_Type_nmi3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_GICR_INMIR0_Type_nmi30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_GICR_INMIR0_Type_nmi30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_GICR_INMIR0_Type_nmi31 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_GICR_INMIR0_Type_nmi31 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_GICR_INMIR0_Type_nmi4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_GICR_INMIR0_Type_nmi4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_GICR_INMIR0_Type_nmi5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_GICR_INMIR0_Type_nmi5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_GICR_INMIR0_Type_nmi6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_GICR_INMIR0_Type_nmi6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_GICR_INMIR0_Type_nmi7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_GICR_INMIR0_Type_nmi7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_GICR_INMIR0_Type_nmi8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_GICR_INMIR0_Type_nmi8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_GICR_INMIR0_Type_nmi9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_GICR_INMIR0_Type_nmi9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def undefined_GICD_CLRSPI_SR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICD_CLRSPI_SR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICV_CTLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICV_CTLR_Type_AckCtl (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_GICV_CTLR_Type_AckCtl (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GICV_CTLR_Type_EnableGrp1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_GICV_CTLR_Type_EnableGrp1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def undefined_GICR_PARTIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_PARTIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDDEVID1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDDEVID1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDDEVID1_Type_HSR (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_EDDEVID1_Type_HSR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def undefined_EDPRCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDPRCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDPRCR_Type_COREPURQ (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_EDPRCR_Type_COREPURQ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_EDPRCR_Type_CWRR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_EDPRCR_Type_CWRR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def undefined_GICR_VSGIPENDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_VSGIPENDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICR_VSGIPENDR_Type_Busy (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_GICR_VSGIPENDR_Type_Busy (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_GICR_SYNCR_Type_Busy (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICR_SYNCR_Type_Busy (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_GICR_VSGIPENDR_Type_Pending (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_GICR_VSGIPENDR_Type_Pending (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def undefined_GICD_STATUSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICD_STATUSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICR_ISENABLER0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_ISENABLER0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICR_ISENABLER0_Type_Set_enable_bit0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_GICR_ISENABLER0_Type_Set_enable_bit0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_GICR_ISENABLER0_Type_Set_enable_bit1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_GICR_ISENABLER0_Type_Set_enable_bit10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_GICR_ISENABLER0_Type_Set_enable_bit11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_GICR_ISENABLER0_Type_Set_enable_bit12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_GICR_ISENABLER0_Type_Set_enable_bit13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_GICR_ISENABLER0_Type_Set_enable_bit14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_GICR_ISENABLER0_Type_Set_enable_bit15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_GICR_ISENABLER0_Type_Set_enable_bit16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_GICR_ISENABLER0_Type_Set_enable_bit17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_GICR_ISENABLER0_Type_Set_enable_bit18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_GICR_ISENABLER0_Type_Set_enable_bit19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_GICR_ISENABLER0_Type_Set_enable_bit2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_GICR_ISENABLER0_Type_Set_enable_bit20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_GICR_ISENABLER0_Type_Set_enable_bit21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_GICR_ISENABLER0_Type_Set_enable_bit22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_GICR_ISENABLER0_Type_Set_enable_bit23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_GICR_ISENABLER0_Type_Set_enable_bit24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_GICR_ISENABLER0_Type_Set_enable_bit25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_GICR_ISENABLER0_Type_Set_enable_bit26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_GICR_ISENABLER0_Type_Set_enable_bit27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_GICR_ISENABLER0_Type_Set_enable_bit28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_GICR_ISENABLER0_Type_Set_enable_bit29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_GICR_ISENABLER0_Type_Set_enable_bit3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_GICR_ISENABLER0_Type_Set_enable_bit30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit31 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_GICR_ISENABLER0_Type_Set_enable_bit31 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_GICR_ISENABLER0_Type_Set_enable_bit4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_GICR_ISENABLER0_Type_Set_enable_bit5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_GICR_ISENABLER0_Type_Set_enable_bit6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_GICR_ISENABLER0_Type_Set_enable_bit7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_GICR_ISENABLER0_Type_Set_enable_bit8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_GICR_ISENABLER0_Type_Set_enable_bit9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_GICR_ISENABLER0_Type_Set_enable_bit9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def undefined_CTICIDR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTICIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTICIDR2_Type_PRMBL_2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_CTICIDR2_Type_PRMBL_2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_AMCIDR2_Type_PRMBL_2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_EDCIDR2_Type_PRMBL_2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_PMCIDR2_Type_PRMBL_2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_AMCIDR2_Type_PRMBL_2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_EDCIDR2_Type_PRMBL_2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_PMCIDR2_Type_PRMBL_2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def undefined_EDRCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDRCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDRCR_Type_CBRRQ (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_EDRCR_Type_CBRRQ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_EDRCR_Type_CSE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_EDRCR_Type_CSE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_EDRCR_Type_CSPA (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_EDRCR_Type_CSPA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def undefined_GICV_PMR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICV_PMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDDEVID_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDDEVID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDDEVID_Type_DebugPower (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_EDDEVID_Type_DebugPower (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def undefined_GICC_DIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_DIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDCIDR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDCIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GITS_MPAMIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GITS_MPAMIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICD_SGIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICD_SGIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICD_SGIR_Type_CPUTargetList (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _update_GICD_SGIR_Type_CPUTargetList (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _get_GICD_SGIR_Type_NSATT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_GICD_SGIR_Type_NSATT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_GICD_SGIR_Type_TargetListFilter (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _update_GICD_SGIR_Type_TargetListFilter (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def undefined_GICH_VMCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICH_VMCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDLAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDLAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICC_AEOIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_AEOIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICC_AHPPIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_AHPPIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICR_SYNCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_SYNCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICC_ABPR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_ABPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CTIPIDR4_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIPIDR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GITS_MPIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GITS_MPIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDCIDR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDCIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICD_SETSPI_NSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICD_SETSPI_NSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CNTID_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CNTID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CNTID_Type_CNTSC (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_CNTID_Type_CNTSC (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def undefined_GITS_IIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GITS_IIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDPIDR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDPIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CTIAUTHSTATUS_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIAUTHSTATUS_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICH_HCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICH_HCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_GICH_HCR_Type_EOICount (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 31 27)

def _update_GICH_HCR_Type_EOICount (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 27 x)

def undefined_GICC_BPR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_BPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CTIDEVID_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIDEVID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTIDEVID_Type_EXTMUXNUM (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _update_CTIDEVID_Type_EXTMUXNUM (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _get_CTIDEVID_Type_INOUT (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _update_CTIDEVID_Type_INOUT (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _get_CTIDEVID_Type_NUMCHAN (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 21 16)

def _update_CTIDEVID_Type_NUMCHAN (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 16 x)

def _get_CTIDEVID_Type_NUMTRIG (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)

def _update_CTIDEVID_Type_NUMTRIG (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 8 x)

def undefined_GICD_SETSPI_SR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICD_SETSPI_SR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICR_STATUSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICR_STATUSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICC_EOIR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_EOIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDPIDR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDPIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CNTNSAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CNTNSAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CNTNSAR_Type_NS2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_CNTNSAR_Type_NS2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_CNTNSAR_Type_NS3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_CNTNSAR_Type_NS3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_CNTNSAR_Type_NS4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_CNTNSAR_Type_NS4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_CNTNSAR_Type_NS5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_CNTNSAR_Type_NS5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_CNTNSAR_Type_NS6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_CNTNSAR_Type_NS6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_CNTNSAR_Type_NS7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_CNTNSAR_Type_NS7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def undefined_EDITCTRL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDITCTRL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICD_IIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICD_IIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_EDCIDR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDCIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_GICC_AIAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_GICC_AIAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMPIDR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMPIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMPIDR4_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMPIDR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMIIDR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMIIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMPIDR3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMPIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMCIDR3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMCIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMDEVARCH_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMDEVARCH_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMPIDR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMPIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMCIDR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMCIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMCIDR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMCIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMPIDR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMPIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMCIDR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMCIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_AMDEVTYPE_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_AMDEVTYPE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def HACTLR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HACTLR2 ) : SailM HACTLR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ACTLR_EL2) 32 32)))

def HACTLR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HACTLR2_Type := value_name
  writeReg ACTLR_EL2 (Sail.BitVec.updateSubrange (← readReg ACTLR_EL2) 63 32 (BitVec.slice r 0 32))
  writeReg _HACTLR2 r

def undefined_PMAUTHSTATUS_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMAUTHSTATUS_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMCGCR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMCGCR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMCIDR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMCIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMCIDR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMCIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMCIDR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMCIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMCIDR3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMCIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMDEVID_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMDEVID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMDEVTYPE_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMDEVTYPE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMITCTRL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMITCTRL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMLAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMLAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMPIDR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMPIDR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMPIDR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMPIDR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMPIDR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMPIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMPIDR3_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMPIDR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMPIDR4_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMPIDR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def __get_ICC_AP0R_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_AP0R_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))

def __get_ESR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ESR_EL1_Type := value_name
  (Mk_ESR_EL1_Type (tmp &&& (Complement.complement 0xFFFFF88000000000#64)))

def __get_ICC_PMR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_PMR_EL1_Type := value_name
  (Mk_ICC_PMR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))

def __get_FPSR (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : FPSR_Type := value_name
  (Mk_FPSR_Type (tmp &&& (Complement.complement 0xFFFFFFFF07FFFF60#64)))

def __get_VBAR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VBAR_EL2_Type := value_name
  (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1F#8 64)))

def __get_ESR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ESR_EL2_Type := value_name
  (Mk_ESR_EL2_Type (tmp &&& (Complement.complement 0xFFFFF80000000000#64)))

def __get_DSPSR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DSPSR_EL0_Type := value_name
  (Mk_DSPSR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFF800000000#64)))

def __get_HFGITR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGITR2_EL2_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFF#64))

def __get_PFAR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PFAR_EL2_Type := value_name
  (Mk_PFAR_EL2_Type (tmp &&& (Complement.complement 0x3F00000000000000#64)))

def __get_MFAR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MFAR_EL3_Type := value_name
  (Mk_MFAR_EL3_Type (tmp &&& (Complement.complement 0x3F00000000000000#64)))

def __get_ICV_AP0R_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_AP0R_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))

def __get_VBAR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VBAR_EL1_Type := value_name
  (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1F#8 64)))

def __get_CNTFRQ_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTFRQ_EL0_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))

def __get_DBGDTRRX_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGDTRRX_EL0_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))

def __get_OSDTRRX_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : OSDTRRX_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))

def __get_PFAR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PFAR_EL1_Type := value_name
  (Mk_PFAR_EL1_Type (tmp &&& (Complement.complement 0x3F00000000000000#64)))

def __get_ESR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ESR_EL3_Type := value_name
  (Mk_ESR_EL3_Type (tmp &&& (Complement.complement 0xFFFFF88000000000#64)))

def __get_OSDTRTX_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : OSDTRTX_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))

def __get_VBAR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VBAR_EL3_Type := value_name
  (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x7FF#12 64)))

def __get_ID_AA64AFR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64AFR1_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFF#64))

def __get_ID_AA64AFR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64AFR0_EL1_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64))

def __get_DBGDSAR (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGDSAR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFF#64))

def __get_GCSPR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSPR_EL3_Type := value_name
  (Mk_GCSPR_EL3_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x7#4 64))))

def __get_GCSPR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSPR_EL1_Type := value_name
  (Mk_GCSPR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x7#4 64))))

def __get_GCSPR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSPR_EL2_Type := value_name
  (Mk_GCSPR_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x7#4 64))))

def __get_GCSPR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSPR_EL0_Type := value_name
  (Mk_GCSPR_EL0_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x7#4 64))))

def __get_JOSCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : JOSCR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))

def __get_HPFAR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HPFAR_Type := value_name
  (Mk_HPFAR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xF#4 32))))

def __get_JIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : JIDR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))

def __get_VBAR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VBAR_Type := value_name
  (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1F#8 32)))

def __get_VBAR_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VBAR_Type := value_name
  (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1F#8 32)))

def __get_VBAR_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VBAR_Type := value_name
  (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1F#8 32)))

def __get_HVBAR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HVBAR_Type := value_name
  (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1F#8 32)))

def __get_FCSEIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : FCSEIDR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))

def __get_JMCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : JMCR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))

def __get_DBGWFAR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGWFAR_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))

def __get_DBGDSCRint (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDSCRint_Type := value_name
  (Mk_DBGDSCRint_Type (tmp &&& (Complement.complement 0x9FF86FC3#32)))

def __get_IFSR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : IFSR_Type := value_name
  (Mk_IFSR_Type (tmp &&& (Complement.complement 0xFFFEE9C0#32)))

def __get_IFSR_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : IFSR_Type := value_name
  (Mk_IFSR_Type (tmp &&& (Complement.complement 0xFFFEE9C0#32)))

def __get_IFSR_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : IFSR_Type := value_name
  (Mk_IFSR_Type (tmp &&& (Complement.complement 0xFFFEE9C0#32)))

def __get_DBGDEVID2 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDEVID2_Type := value_name
  (tmp &&& (Complement.complement 0xFFFFFFFF#32))

def __get_DSPSR2 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DSPSR2_Type := value_name
  (Mk_DSPSR2_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

/-- Type quantifiers: M : Nat, N : Nat, i : Int, M ≥ 0 ∧ N ≥ 0 -/
def ZeroUnsignedSatQ (i : Int) (N : Nat) (M : Nat) : SailM ((BitVec M) × Bool) := do
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let saturated ← (( do (undefined_bool ()) ) : SailM Bool )
  let (result, saturated) : (Int × Bool) :=
    if ((i >b ((2 ^i N) -i 1)) : Bool)
    then
      (let result : Int := ((2 ^i N) -i 1)
      let saturated : Bool := true
      (result, saturated))
    else
      (let (result, saturated) : (Int × Bool) :=
        if ((i <b 0) : Bool)
        then
          (let result : Int := 0
          let saturated : Bool := true
          (result, saturated))
        else
          (let result : Int := i
          let saturated : Bool := false
          (result, saturated))
      (result, saturated))
  let result := result
  let fullresult : (BitVec M) := (Zeros (n := M))
  let fullresult ← (( do
    if ((N >b 0) : Bool)
    then
      (do
        sail_assert ((0 ≤b (N -i 1)) && ((N -i 1) <b M)) "src/v8_base.sail:57129.54-57129.55"
        (pure (Sail.BitVec.updateSubrange fullresult (N -i 1) 0 (integer_subrange result (N -i 1) 0))))
    else (pure fullresult) ) : SailM (BitVec M) )
  (pure (fullresult, saturated))

def _set_Configuration_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_bits r v)

def _set_ACCDATA_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ACCDATA_EL1_Type_bits r v)

def _set_AMCFGR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCFGR_EL0_Type_bits r v)

def _set_AMCFGR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCFGR_Type_bits r v)

def _set_AMCG1IDR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_bits r v)

def _set_AMCGCR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCGCR_EL0_Type_bits r v)

def _set_AMCGCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCGCR_Type_bits r v)

def _set_AMCIDR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCIDR0_Type_bits r v)

def _set_AMCIDR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCIDR1_Type_bits r v)

def _set_AMCIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCIDR2_Type_bits r v)

def _set_AMCIDR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCIDR3_Type_bits r v)

def _set_AMCNTENCLR0_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR0_EL0_Type_bits r v)

def _set_AMCNTENCLR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR0_Type_bits r v)

def _set_AMCNTENCLR1_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_bits r v)

def _set_AMCNTENCLR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_bits r v)

def _set_AMCNTENSET0_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET0_EL0_Type_bits r v)

def _set_AMCNTENSET0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET0_Type_bits r v)

def _set_AMCNTENSET1_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_bits r v)

def _set_AMCNTENSET1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_bits r v)

def _set_AMCR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCR_EL0_Type_bits r v)

def _set_AMCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCR_Type_bits r v)

def _set_AMDEVARCH_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMDEVARCH_Type_bits r v)

def _set_AMDEVTYPE_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMDEVTYPE_Type_bits r v)

def _set_AMEVCNTR0_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVCNTR0_EL0_Type_bits r v)

def _set_AMEVCNTR0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVCNTR0_Type_bits r v)

def _set_AMEVCNTR1_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVCNTR1_EL0_Type_bits r v)

def _set_AMEVCNTR1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVCNTR1_Type_bits r v)

def _set_AMEVTYPER0_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVTYPER0_EL0_Type_bits r v)

def _set_AMEVTYPER0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVTYPER0_Type_bits r v)

def _set_AMEVTYPER1_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVTYPER1_EL0_Type_bits r v)

def _set_AMEVTYPER1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVTYPER1_Type_bits r v)

def _set_AMIIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMIIDR_Type_bits r v)

def _set_AMPIDR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR0_Type_bits r v)

def _set_AMPIDR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR1_Type_bits r v)

def _set_AMPIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR2_Type_bits r v)

def _set_AMPIDR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR3_Type_bits r v)

def _set_AMPIDR4_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR4_Type_bits r v)

def _set_AMUSERENR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMUSERENR_EL0_Type_bits r v)

def _set_AMUSERENR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMUSERENR_Type_bits r v)

def _set_BRBCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL1_Type_bits r v)

def _set_BRBCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL2_Type_bits r v)

def _set_BRBFCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_bits r v)

def _set_BRBIDR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBIDR0_EL1_Type_bits r v)

def _set_BRBINFINJ_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_bits r v)

def _set_BRBINFType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFType_bits r v)

def _set_BRBINF_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINF_EL1_Type_bits r v)

def _set_BRBSRCINJ_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBSRCINJ_EL1_Type_bits r v)

def _set_BRBSRCType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBSRCType_bits r v)

def _set_BRBSRC_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBSRC_EL1_Type_bits r v)

def _set_BRBTGTINJ_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBTGTINJ_EL1_Type_bits r v)

def _set_BRBTGTType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBTGTType_bits r v)

def _set_BRBTGT_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBTGT_EL1_Type_bits r v)

def _set_BRBTS_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBTS_EL1_Type_bits r v)

def _set_CCSIDR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR2_EL1_Type_bits r v)

def _set_CCSIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR2_Type_bits r v)

def _set_CCSIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR_EL1_Type_bits r v)

def _set_CCSIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR_Type_bits r v)

def _set_CLIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_bits r v)

def _set_CLIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_bits r v)

def _set_CNTCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTCR_Type_bits r v)

def _set_CNTEL0ACR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTEL0ACR_Type_bits r v)

def _set_CNTFID0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTFID0_Type_bits r v)

def _set_CNTHCTL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_bits r v)

def _set_CNTHCTL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_Type_bits r v)

def _set_CNTHPS_CTL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_CTL_EL2_Type_bits r v)

def _set_CNTHPS_CTL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_CTL_Type_bits r v)

def _set_CNTHPS_CVAL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_CVAL_EL2_Type_bits r v)

def _set_CNTHPS_TVAL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_TVAL_EL2_Type_bits r v)

def _set_CNTHP_CTL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CTL_EL2_Type_bits r v)

def _set_CNTHP_CTL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CTL_Type_bits r v)

def _set_CNTHP_CVAL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CVAL_EL2_Type_bits r v)

def _set_CNTHP_CVAL_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CVAL_Type_bits r v)

def _set_CNTHP_TVAL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_TVAL_EL2_Type_bits r v)

def _set_CNTHVS_CTL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_CTL_EL2_Type_bits r v)

def _set_CNTHVS_CTL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_CTL_Type_bits r v)

def _set_CNTHVS_CVAL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_CVAL_EL2_Type_bits r v)

def _set_CNTHVS_TVAL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_TVAL_EL2_Type_bits r v)

def _set_CNTHV_CTL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_CTL_EL2_Type_bits r v)

def _set_CNTHV_CTL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_CTL_Type_bits r v)

def _set_CNTHV_CVAL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_CVAL_EL2_Type_bits r v)

def _set_CNTHV_TVAL_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_TVAL_EL2_Type_bits r v)

def _set_CNTID_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTID_Type_bits r v)

def _set_CNTKCTL_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_bits r v)

def _set_CNTKCTL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_Type_bits r v)

def _set_CNTNSAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTNSAR_Type_bits r v)

def _set_CNTPS_CTL_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTPS_CTL_EL1_Type_bits r v)

def _set_CNTPS_CVAL_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTPS_CVAL_EL1_Type_bits r v)

def _set_CNTPS_TVAL_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTPS_TVAL_EL1_Type_bits r v)

def _set_CNTP_CTL_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CTL_EL0_Type_bits r v)

def _set_CNTP_CTL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CTL_Type_bits r v)

def _set_CNTP_CVAL_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CVAL_EL0_Type_bits r v)

def _set_CNTP_CVAL_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CVAL_Type_bits r v)

def _set_CNTP_TVAL_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_TVAL_EL0_Type_bits r v)

def _set_CNTSCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTSCR_Type_bits r v)

def _set_CNTSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTSR_Type_bits r v)

def _set_CNTV_CTL_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CTL_EL0_Type_bits r v)

def _set_CNTV_CTL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CTL_Type_bits r v)

def _set_CNTV_CVAL_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CVAL_EL0_Type_bits r v)

def _set_CNTV_CVAL_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CVAL_Type_bits r v)

def _set_CNTV_TVAL_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_TVAL_EL0_Type_bits r v)

def _set_CONTEXTIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CONTEXTIDR_EL1_Type_bits r v)

def _set_CONTEXTIDR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CONTEXTIDR_EL2_Type_bits r v)

def _set_CONTEXTIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CONTEXTIDR_Type_bits r v)

def _set_CPACR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_EL1_Type_bits r v)

def _set_CPACR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_Type_bits r v)

def _set_CPTR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL2_Type_bits r v)

def _set_CPTR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL3_Type_bits r v)

def _set_CSSELR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CSSELR_EL1_Type_bits r v)

def _set_CSSELR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CSSELR_Type_bits r v)

def _set_CTIAUTHSTATUS_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIAUTHSTATUS_Type_bits r v)

def _set_CTICIDR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICIDR0_Type_bits r v)

def _set_CTICIDR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICIDR1_Type_bits r v)

def _set_CTICIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICIDR2_Type_bits r v)

def _set_CTICIDR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICIDR3_Type_bits r v)

def _set_CTICONTROL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICONTROL_Type_bits r v)

def _set_CTIDEVARCH_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVARCH_Type_bits r v)

def _set_CTIDEVCTL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVCTL_Type_bits r v)

def _set_CTIDEVID_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVID_Type_bits r v)

def _set_CTIDEVTYPE_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVTYPE_Type_bits r v)

def _set_CTIITCTRL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIITCTRL_Type_bits r v)

def _set_CTILAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTILAR_Type_bits r v)

def _set_CTILSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTILSR_Type_bits r v)

def _set_CTIPIDR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR0_Type_bits r v)

def _set_CTIPIDR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR1_Type_bits r v)

def _set_CTIPIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR2_Type_bits r v)

def _set_CTIPIDR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR3_Type_bits r v)

def _set_CTIPIDR4_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR4_Type_bits r v)

def _set_CTR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_EL0_Type_bits r v)

def _set_CTR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_Type_bits r v)

def _set_DACR32_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_bits r v)

def _set_DACR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_bits r v)

def _set_DBGAUTHSTATUS_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_bits r v)

def _set_DBGAUTHSTATUS_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_Type_bits r v)

def _set_DBGBCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_bits r v)

def _set_DBGBCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_Type_bits r v)

def _set_DBGBVR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_bits r v)

def _set_DBGBVR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBVR_Type_bits r v)

def _set_DBGBXVR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBXVR_Type_bits r v)

def _set_DBGCLAIMCLR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGCLAIMCLR_EL1_Type_bits r v)

def _set_DBGCLAIMCLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGCLAIMCLR_Type_bits r v)

def _set_DBGCLAIMSET_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGCLAIMSET_EL1_Type_bits r v)

def _set_DBGCLAIMSET_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGCLAIMSET_Type_bits r v)

def _set_DBGDCCINT_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDCCINT_Type_bits r v)

def _set_DBGDEVID1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID1_Type_bits r v)

def _set_DBGDEVID_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID_Type_bits r v)

def _set_DBGDIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDIDR_Type_bits r v)

def _set_DBGDRAR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDRAR_Type_bits r v)

def _set_DBGDSCRext_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_bits r v)

def _set_DBGDSCRint_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRint_Type_bits r v)

def _set_DBGDTRRXext_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTRRXext_Type_bits r v)

def _set_DBGDTRRXint_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTRRXint_Type_bits r v)

def _set_DBGDTRTXext_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTRTXext_Type_bits r v)

def _set_DBGDTRTXint_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTRTXint_Type_bits r v)

def _set_DBGDTR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTR_EL0_Type_bits r v)

def _set_DBGOSDLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGOSDLR_Type_bits r v)

def _set_DBGOSECCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGOSECCR_Type_bits r v)

def _set_DBGOSLAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGOSLAR_Type_bits r v)

def _set_DBGOSLSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGOSLSR_Type_bits r v)

def _set_DBGPRCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGPRCR_EL1_Type_bits r v)

def _set_DBGPRCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGPRCR_Type_bits r v)

def _set_DBGVCR32_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_bits r v)

def _set_DBGVCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_bits r v)

def _set_DBGWCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_bits r v)

def _set_DBGWCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_Type_bits r v)

def _set_DBGWVR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWVR_EL1_Type_bits r v)

def _set_DBGWVR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWVR_Type_bits r v)

def _set_DCZID_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DCZID_EL0_Type_bits r v)

def _set_DFSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DFSR_Type_bits r v)

def _set_DISR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_EL1_Type_bits r v)

def _set_DISR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_Type_bits r v)

def _set_DSPSR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR2_Type_bits r v)

def _set_DSPSR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_bits r v)

def _set_DSPSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_bits r v)

def _set_DormantCtl_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_bits r v)

def _set_EDAA32PFR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDAA32PFR_Type_bits r v)

def _set_EDCIDR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDCIDR0_Type_bits r v)

def _set_EDCIDR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDCIDR1_Type_bits r v)

def _set_EDCIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDCIDR2_Type_bits r v)

def _set_EDCIDR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDCIDR3_Type_bits r v)

def _set_EDDEVARCH_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVARCH_Type_bits r v)

def _set_EDDEVID1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVID1_Type_bits r v)

def _set_EDDEVID_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVID_Type_bits r v)

def _set_EDDEVTYPE_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVTYPE_Type_bits r v)

def _set_EDDFR1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_bits r v)

def _set_EDDFR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR_Type_bits r v)

def _set_EDECCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_bits r v)

def _set_EDECR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECR_Type_bits r v)

def _set_EDESR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDESR_Type_bits r v)

def _set_EDHSR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDHSR_Type_bits r v)

def _set_EDITCTRL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDITCTRL_Type_bits r v)

def _set_EDLAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDLAR_Type_bits r v)

def _set_EDLSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDLSR_Type_bits r v)

def _set_EDPCSR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPCSR_Type_bits r v)

def _set_EDPFR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_bits r v)

def _set_EDPIDR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR0_Type_bits r v)

def _set_EDPIDR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR1_Type_bits r v)

def _set_EDPIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR2_Type_bits r v)

def _set_EDPIDR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR3_Type_bits r v)

def _set_EDPIDR4_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR4_Type_bits r v)

def _set_EDPRCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRCR_Type_bits r v)

def _set_EDPRSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_bits r v)

def _set_EDRCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDRCR_Type_bits r v)

def _set_EDSCR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR2_Type_bits r v)

def _set_EDSCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_bits r v)

def _set_EDVIDSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDVIDSR_Type_bits r v)

def _set_ERRIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRIDR_EL1_Type_bits r v)

def _set_ERRIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRIDR_Type_bits r v)

def _set_ERRSELR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRSELR_EL1_Type_bits r v)

def _set_ERRSELR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRSELR_Type_bits r v)

def _set_ERRnFR_ElemType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_bits r v)

def _set_ERXGSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_bits r v)

def _set_ESRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESRType_bits r v)

def _set_ESR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL1_Type_bits r v)

def _set_ESR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL2_Type_bits r v)

def _set_ESR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL3_Type_bits r v)

def _set_FPCRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_bits r v)

def _set_FPCR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_bits r v)

def _set_FPEXC32_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_bits r v)

def _set_FPEXC_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_bits r v)

def _set_FPSCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_bits r v)

def _set_FPSID_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSID_Type_bits r v)

def _set_FPSR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_bits r v)

def _set_GCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCR_EL1_Type_bits r v)

def _set_GCSCRE0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_bits r v)

def _set_GCSCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL1_Type_bits r v)

def _set_GCSCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL2_Type_bits r v)

def _set_GCSCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL3_Type_bits r v)

def _set_GCSPR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSPR_EL0_Type_bits r v)

def _set_GCSPR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSPR_EL1_Type_bits r v)

def _set_GCSPR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSPR_EL2_Type_bits r v)

def _set_GCSPR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSPR_EL3_Type_bits r v)

def _set_GICC_ABPR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_ABPR_Type_bits r v)

def _set_GICC_AEOIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_AEOIR_Type_bits r v)

def _set_GICC_AHPPIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_AHPPIR_Type_bits r v)

def _set_GICC_AIAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_AIAR_Type_bits r v)

def _set_GICC_BPR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_BPR_Type_bits r v)

def _set_GICC_CTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_CTLR_Type_bits r v)

def _set_GICC_DIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_DIR_Type_bits r v)

def _set_GICC_EOIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_EOIR_Type_bits r v)

def _set_GICC_HPPIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_HPPIR_Type_bits r v)

def _set_GICC_IAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_IAR_Type_bits r v)

def _set_GICC_PMR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_PMR_Type_bits r v)

def _set_GICC_RPR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_RPR_Type_bits r v)

def _set_GICC_STATUSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_STATUSR_Type_bits r v)

def _set_GICD_CLRSPI_NSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CLRSPI_NSR_Type_bits r v)

def _set_GICD_CLRSPI_SR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CLRSPI_SR_Type_bits r v)

def _set_GICD_CTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_bits r v)

def _set_GICD_IIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_IIDR_Type_bits r v)

def _set_GICD_SETSPI_NSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_SETSPI_NSR_Type_bits r v)

def _set_GICD_SETSPI_SR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_SETSPI_SR_Type_bits r v)

def _set_GICD_SGIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_SGIR_Type_bits r v)

def _set_GICD_STATUSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_STATUSR_Type_bits r v)

def _set_GICD_TYPER2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER2_Type_bits r v)

def _set_GICD_TYPER_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_bits r v)

def _set_GICH_EISR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_bits r v)

def _set_GICH_ELRSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_bits r v)

def _set_GICH_HCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_HCR_Type_bits r v)

def _set_GICH_MISR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_MISR_Type_bits r v)

def _set_GICH_VMCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VMCR_Type_bits r v)

def _set_GICH_VTR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VTR_Type_bits r v)

def _set_GICM_CLRSPI_NSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_CLRSPI_NSR_Type_bits r v)

def _set_GICM_CLRSPI_SR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_CLRSPI_SR_Type_bits r v)

def _set_GICM_IIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_IIDR_Type_bits r v)

def _set_GICM_SETSPI_NSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_SETSPI_NSR_Type_bits r v)

def _set_GICM_SETSPI_SR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_SETSPI_SR_Type_bits r v)

def _set_GICM_TYPER_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_TYPER_Type_bits r v)

def _set_GICR_CLRLPIR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CLRLPIR_Type_bits r v)

def _set_GICR_CTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CTLR_Type_bits r v)

def _set_GICR_IIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_IIDR_Type_bits r v)

def _set_GICR_INMIR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_bits r v)

def _set_GICR_INVALLR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INVALLR_Type_bits r v)

def _set_GICR_INVLPIR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INVLPIR_Type_bits r v)

def _set_GICR_ISENABLER0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_bits r v)

def _set_GICR_MPAMIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_MPAMIDR_Type_bits r v)

def _set_GICR_PARTIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PARTIDR_Type_bits r v)

def _set_GICR_PENDBASER_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_bits r v)

def _set_GICR_PROPBASER_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PROPBASER_Type_bits r v)

def _set_GICR_SETLPIR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_SETLPIR_Type_bits r v)

def _set_GICR_STATUSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_STATUSR_Type_bits r v)

def _set_GICR_SYNCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_SYNCR_Type_bits r v)

def _set_GICR_VPENDBASER_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_bits r v)

def _set_GICR_VPROPBASER_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_bits r v)

def _set_GICR_VSGIPENDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VSGIPENDR_Type_bits r v)

def _set_GICR_VSGIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VSGIR_Type_bits r v)

def _set_GICR_WAKER_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_WAKER_Type_bits r v)

def _set_GICV_ABPR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_ABPR_Type_bits r v)

def _set_GICV_AEOIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_AEOIR_Type_bits r v)

def _set_GICV_AHPPIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_AHPPIR_Type_bits r v)

def _set_GICV_AIAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_AIAR_Type_bits r v)

def _set_GICV_BPR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_BPR_Type_bits r v)

def _set_GICV_CTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_CTLR_Type_bits r v)

def _set_GICV_DIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_DIR_Type_bits r v)

def _set_GICV_EOIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_EOIR_Type_bits r v)

def _set_GICV_HPPIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_HPPIR_Type_bits r v)

def _set_GICV_IAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_IAR_Type_bits r v)

def _set_GICV_PMR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_PMR_Type_bits r v)

def _set_GICV_RPR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_RPR_Type_bits r v)

def _set_GICV_STATUSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_STATUSR_Type_bits r v)

def _set_GITS_CBASER_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CBASER_Type_bits r v)

def _set_GITS_CREADR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CREADR_Type_bits r v)

def _set_GITS_CTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CTLR_Type_bits r v)

def _set_GITS_CWRITER_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CWRITER_Type_bits r v)

def _set_GITS_IIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_IIDR_Type_bits r v)

def _set_GITS_MPAMIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_MPAMIDR_Type_bits r v)

def _set_GITS_MPIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_MPIDR_Type_bits r v)

def _set_GITS_PARTIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_PARTIDR_Type_bits r v)

def _set_GITS_SGIR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_SGIR_Type_bits r v)

def _set_GITS_STATUSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_STATUSR_Type_bits r v)

def _set_GITS_TYPER_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_bits r v)

def _set_GMID_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GMID_EL1_Type_bits r v)

def _set_GPCCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPCCR_EL3_Type_bits r v)

def _set_GPTBR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPTBR_EL3_Type_bits r v)

def _set_HAFGRTR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_bits r v)

def _set_HCPTR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCPTR_Type_bits r v)

def _set_HCR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR2_Type_bits r v)

def _set_HCRX_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_bits r v)

def _set_HCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_bits r v)

def _set_HCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_bits r v)

def _set_HDCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_bits r v)

def _set_HDFGRTR2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_bits r v)

def _set_HDFGRTR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_bits r v)

def _set_HDFGWTR2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_bits r v)

def _set_HDFGWTR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_bits r v)

def _set_HFGITR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_bits r v)

def _set_HFGRTR2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR2_EL2_Type_bits r v)

def _set_HFGRTR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_bits r v)

def _set_HFGWTR2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR2_EL2_Type_bits r v)

def _set_HFGWTR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_bits r v)

def _set_HMAIR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HMAIR0_Type_bits r v)

def _set_HMAIR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HMAIR1_Type_bits r v)

def _set_HPFAR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HPFAR_EL2_Type_bits r v)

def _set_HPFAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HPFAR_Type_bits r v)

def _set_HRMR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HRMR_Type_bits r v)

def _set_HSCTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_bits r v)

def _set_HSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSR_Type_bits r v)

def _set_HSTR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_bits r v)

def _set_HSTR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_bits r v)

def _set_HTCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTCR_Type_bits r v)

def _set_HTRFCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTRFCR_Type_bits r v)

def _set_HTTBR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTTBR_Type_bits r v)

def _set_ICC_AP1R_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_AP1R_EL1_Type_bits r v)

def _set_ICC_ASGI1R_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_bits r v)

def _set_ICC_ASGI1R_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_bits r v)

def _set_ICC_BPR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_BPR0_EL1_Type_bits r v)

def _set_ICC_BPR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_BPR0_Type_bits r v)

def _set_ICC_BPR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_BPR1_EL1_Type_bits r v)

def _set_ICC_BPR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_BPR1_Type_bits r v)

def _set_ICC_CTLR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL1_Type_bits r v)

def _set_ICC_CTLR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_bits r v)

def _set_ICC_CTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_Type_bits r v)

def _set_ICC_DIR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_DIR_EL1_Type_bits r v)

def _set_ICC_DIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_DIR_Type_bits r v)

def _set_ICC_EOIR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_EOIR0_EL1_Type_bits r v)

def _set_ICC_EOIR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_EOIR0_Type_bits r v)

def _set_ICC_EOIR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_EOIR1_EL1_Type_bits r v)

def _set_ICC_EOIR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_EOIR1_Type_bits r v)

def _set_ICC_HPPIR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HPPIR0_EL1_Type_bits r v)

def _set_ICC_HPPIR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HPPIR0_Type_bits r v)

def _set_ICC_HPPIR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HPPIR1_EL1_Type_bits r v)

def _set_ICC_HPPIR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HPPIR1_Type_bits r v)

def _set_ICC_HSRE_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HSRE_Type_bits r v)

def _set_ICC_IAR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IAR0_EL1_Type_bits r v)

def _set_ICC_IAR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IAR0_Type_bits r v)

def _set_ICC_IAR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IAR1_EL1_Type_bits r v)

def _set_ICC_IAR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IAR1_Type_bits r v)

def _set_ICC_IGRPEN0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN0_EL1_Type_bits r v)

def _set_ICC_IGRPEN0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN0_Type_bits r v)

def _set_ICC_IGRPEN1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN1_EL1_Type_bits r v)

def _set_ICC_IGRPEN1_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN1_EL3_Type_bits r v)

def _set_ICC_IGRPEN1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN1_Type_bits r v)

def _set_ICC_MCTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_bits r v)

def _set_ICC_MGRPEN1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MGRPEN1_Type_bits r v)

def _set_ICC_MSRE_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MSRE_Type_bits r v)

def _set_ICC_NMIAR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_NMIAR1_EL1_Type_bits r v)

def _set_ICC_PMR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_PMR_EL1_Type_bits r v)

def _set_ICC_PMR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_PMR_Type_bits r v)

def _set_ICC_RPR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_RPR_EL1_Type_bits r v)

def _set_ICC_RPR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_RPR_Type_bits r v)

def _set_ICC_SGI0R_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_bits r v)

def _set_ICC_SGI0R_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_Type_bits r v)

def _set_ICC_SGI1R_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_bits r v)

def _set_ICC_SGI1R_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_Type_bits r v)

def _set_ICC_SRE_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL1_Type_bits r v)

def _set_ICC_SRE_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL2_Type_bits r v)

def _set_ICC_SRE_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL3_Type_bits r v)

def _set_ICC_SRE_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_Type_bits r v)

def _set_ICH_AP0R_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_bits r v)

def _set_ICH_AP0R_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_bits r v)

def _set_ICH_AP1R_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_bits r v)

def _set_ICH_AP1R_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_bits r v)

def _set_ICH_EISR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_bits r v)

def _set_ICH_EISR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_bits r v)

def _set_ICH_ELRSR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_bits r v)

def _set_ICH_ELRSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_bits r v)

def _set_ICH_HCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_bits r v)

def _set_ICH_HCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_bits r v)

def _set_ICH_LRC_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LRC_Type_bits r v)

def _set_ICH_LR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_bits r v)

def _set_ICH_LR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LR_Type_bits r v)

def _set_ICH_MISR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_EL2_Type_bits r v)

def _set_ICH_MISR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_Type_bits r v)

def _set_ICH_VMCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_bits r v)

def _set_ICH_VMCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_Type_bits r v)

def _set_ICH_VTR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_bits r v)

def _set_ICH_VTR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_Type_bits r v)

def _set_ICV_AP1R_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_AP1R_EL1_Type_bits r v)

def _set_ICV_BPR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_BPR0_EL1_Type_bits r v)

def _set_ICV_BPR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_BPR0_Type_bits r v)

def _set_ICV_BPR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_BPR1_EL1_Type_bits r v)

def _set_ICV_BPR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_BPR1_Type_bits r v)

def _set_ICV_CTLR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_EL1_Type_bits r v)

def _set_ICV_CTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_Type_bits r v)

def _set_ICV_DIR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_DIR_EL1_Type_bits r v)

def _set_ICV_DIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_DIR_Type_bits r v)

def _set_ICV_EOIR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_EOIR0_EL1_Type_bits r v)

def _set_ICV_EOIR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_EOIR0_Type_bits r v)

def _set_ICV_EOIR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_EOIR1_EL1_Type_bits r v)

def _set_ICV_EOIR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_EOIR1_Type_bits r v)

def _set_ICV_HPPIR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_HPPIR0_EL1_Type_bits r v)

def _set_ICV_HPPIR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_HPPIR0_Type_bits r v)

def _set_ICV_HPPIR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_HPPIR1_EL1_Type_bits r v)

def _set_ICV_HPPIR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_HPPIR1_Type_bits r v)

def _set_ICV_IAR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IAR0_EL1_Type_bits r v)

def _set_ICV_IAR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IAR0_Type_bits r v)

def _set_ICV_IAR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IAR1_EL1_Type_bits r v)

def _set_ICV_IAR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IAR1_Type_bits r v)

def _set_ICV_IGRPEN0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IGRPEN0_EL1_Type_bits r v)

def _set_ICV_IGRPEN0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IGRPEN0_Type_bits r v)

def _set_ICV_IGRPEN1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IGRPEN1_EL1_Type_bits r v)

def _set_ICV_IGRPEN1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IGRPEN1_Type_bits r v)

def _set_ICV_NMIAR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_NMIAR1_EL1_Type_bits r v)

def _set_ICV_PMR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_PMR_EL1_Type_bits r v)

def _set_ICV_PMR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_PMR_Type_bits r v)

def _set_ICV_RPR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_RPR_EL1_Type_bits r v)

def _set_ICV_RPR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_RPR_Type_bits r v)

def _set_ID_AA64DFR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_bits r v)

def _set_ID_AA64DFR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_bits r v)

def _set_ID_AA64ISAR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_bits r v)

def _set_ID_AA64ISAR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_bits r v)

def _set_ID_AA64ISAR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_bits r v)

def _set_ID_AA64MMFR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_bits r v)

def _set_ID_AA64MMFR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_bits r v)

def _set_ID_AA64MMFR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_bits r v)

def _set_ID_AA64MMFR3_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_bits r v)

def _set_ID_AA64MMFR4_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR4_EL1_Type_bits r v)

def _set_ID_AA64PFR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_bits r v)

def _set_ID_AA64PFR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_bits r v)

def _set_ID_AA64PFR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR2_EL1_Type_bits r v)

def _set_ID_AA64SMFR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_bits r v)

def _set_ID_AA64ZFR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_bits r v)

def _set_ID_DFR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_bits r v)

def _set_ID_DFR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_Type_bits r v)

def _set_ID_DFR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR1_EL1_Type_bits r v)

def _set_ID_DFR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR1_Type_bits r v)

def _set_ID_ISAR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_bits r v)

def _set_ID_ISAR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_Type_bits r v)

def _set_ID_ISAR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_EL1_Type_bits r v)

def _set_ID_ISAR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_Type_bits r v)

def _set_ID_ISAR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_bits r v)

def _set_ID_ISAR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_Type_bits r v)

def _set_ID_ISAR3_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_EL1_Type_bits r v)

def _set_ID_ISAR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_Type_bits r v)

def _set_ID_ISAR4_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_EL1_Type_bits r v)

def _set_ID_ISAR4_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_Type_bits r v)

def _set_ID_ISAR5_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_EL1_Type_bits r v)

def _set_ID_ISAR5_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_Type_bits r v)

def _set_ID_ISAR6_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_bits r v)

def _set_ID_ISAR6_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_Type_bits r v)

def _set_ID_MMFR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_bits r v)

def _set_ID_MMFR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_Type_bits r v)

def _set_ID_MMFR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_bits r v)

def _set_ID_MMFR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_Type_bits r v)

def _set_ID_MMFR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_bits r v)

def _set_ID_MMFR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_Type_bits r v)

def _set_ID_MMFR3_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_EL1_Type_bits r v)

def _set_ID_MMFR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_Type_bits r v)

def _set_ID_MMFR4_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_bits r v)

def _set_ID_MMFR4_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_Type_bits r v)

def _set_ID_MMFR5_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR5_EL1_Type_bits r v)

def _set_ID_MMFR5_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR5_Type_bits r v)

def _set_ID_PFR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_bits r v)

def _set_ID_PFR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_Type_bits r v)

def _set_ID_PFR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_bits r v)

def _set_ID_PFR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_Type_bits r v)

def _set_ID_PFR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR2_EL1_Type_bits r v)

def _set_ID_PFR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR2_Type_bits r v)

def _set_IFSR32_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR32_EL2_Type_bits r v)

def _set_IFSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR_Type_bits r v)

def _set_ISR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ISR_EL1_Type_bits r v)

def _set_ISR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ISR_Type_bits r v)

def _set_LORC_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORC_EL1_Type_bits r v)

def _set_LOREA_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LOREA_EL1_Type_bits r v)

def _set_LORID_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORID_EL1_Type_bits r v)

def _set_LORN_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORN_EL1_Type_bits r v)

def _set_LORSA_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORSA_EL1_Type_bits r v)

def _set_MAIR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR0_Type_bits r v)

def _set_MAIR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR1_Type_bits r v)

def _set_MAIR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL1_Type_bits r v)

def _set_MAIR2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL2_Type_bits r v)

def _set_MAIR2_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL3_Type_bits r v)

def _set_MAIRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIRType_bits r v)

def _set_MAIR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL1_Type_bits r v)

def _set_MAIR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL2_Type_bits r v)

def _set_MAIR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL3_Type_bits r v)

def _set_MDCCINT_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCCINT_EL1_Type_bits r v)

def _set_MDCCSR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCCSR_EL0_Type_bits r v)

def _set_MDCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_bits r v)

def _set_MDCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_bits r v)

def _set_MDRAR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDRAR_EL1_Type_bits r v)

def _set_MDSCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_bits r v)

def _set_MDSELR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSELR_EL1_Type_bits r v)

def _set_MECIDR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECIDR_EL2_Type_bits r v)

def _set_MECID_A0_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECID_A0_EL2_Type_bits r v)

def _set_MECID_A1_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECID_A1_EL2_Type_bits r v)

def _set_MECID_P0_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECID_P0_EL2_Type_bits r v)

def _set_MECID_P1_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECID_P1_EL2_Type_bits r v)

def _set_MECID_RL_A_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECID_RL_A_EL3_Type_bits r v)

def _set_MFAR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MFAR_EL3_Type_bits r v)

def _set_MIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_EL1_Type_bits r v)

def _set_MIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_Type_bits r v)

def _set_MPAM0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM0_EL1_Type_bits r v)

def _set_MPAM1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM1_EL1_Type_bits r v)

def _set_MPAM2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_bits r v)

def _set_MPAM3_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_bits r v)

def _set_MPAMHCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMHCR_EL2_Type_bits r v)

def _set_MPAMIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_bits r v)

def _set_MPAMSM_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMSM_EL1_Type_bits r v)

def _set_MPAMVPM0_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM0_EL2_Type_bits r v)

def _set_MPAMVPM1_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM1_EL2_Type_bits r v)

def _set_MPAMVPM2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM2_EL2_Type_bits r v)

def _set_MPAMVPM3_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM3_EL2_Type_bits r v)

def _set_MPAMVPM4_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM4_EL2_Type_bits r v)

def _set_MPAMVPM5_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM5_EL2_Type_bits r v)

def _set_MPAMVPM6_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM6_EL2_Type_bits r v)

def _set_MPAMVPM7_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM7_EL2_Type_bits r v)

def _set_MPAMVPMV_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_bits r v)

def _set_MPIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_EL1_Type_bits r v)

def _set_MPIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_Type_bits r v)

def _set_MVBAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVBAR_Type_bits r v)

def _set_MVFR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_EL1_Type_bits r v)

def _set_MVFR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_Type_bits r v)

def _set_MVFR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_EL1_Type_bits r v)

def _set_MVFR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_Type_bits r v)

def _set_MVFR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR2_EL1_Type_bits r v)

def _set_MVFR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR2_Type_bits r v)

def _set_NMRR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_bits r v)

def _set_NSACR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NSACR_Type_bits r v)

def _set_OSDLR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_OSDLR_EL1_Type_bits r v)

def _set_OSECCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_OSECCR_EL1_Type_bits r v)

def _set_OSLAR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_OSLAR_EL1_Type_bits r v)

def _set_OSLSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_OSLSR_EL1_Type_bits r v)

def _set_PAR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_bits r v)

def _set_PAR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_bits r v)

def _set_PFAR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PFAR_EL1_Type_bits r v)

def _set_PFAR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PFAR_EL2_Type_bits r v)

def _set_PIRE0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_bits r v)

def _set_PIRE0_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_bits r v)

def _set_PIR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_bits r v)

def _set_PIR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_bits r v)

def _set_PIR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_bits r v)

def _set_PMAUTHSTATUS_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_bits r v)

def _set_PMBIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBIDR_EL1_Type_bits r v)

def _set_PMBLIMITR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBLIMITR_EL1_Type_bits r v)

def _set_PMBPTR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBPTR_EL1_Type_bits r v)

def _set_PMBSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBSR_EL1_Type_bits r v)

def _set_PMCCFILTR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_bits r v)

def _set_PMCCFILTR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_Type_bits r v)

def _set_PMCCNTR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCNTR_EL0_Type_bits r v)

def _set_PMCCNTR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCNTR_Type_bits r v)

def _set_PMCCNTSVR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCNTSVR_EL1_Type_bits r v)

def _set_PMCEID0_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_bits r v)

def _set_PMCEID0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_bits r v)

def _set_PMCEID1_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_bits r v)

def _set_PMCEID1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_bits r v)

def _set_PMCEID2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_bits r v)

def _set_PMCEID3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_bits r v)

def _set_PMCFGR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_bits r v)

def _set_PMCGCR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCGCR0_Type_bits r v)

def _set_PMCIDR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCIDR0_Type_bits r v)

def _set_PMCIDR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCIDR1_Type_bits r v)

def _set_PMCIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCIDR2_Type_bits r v)

def _set_PMCIDR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCIDR3_Type_bits r v)

def _set_PMCNTENCLR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_bits r v)

def _set_PMCNTENCLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_bits r v)

def _set_PMCNTENSET_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_bits r v)

def _set_PMCNTENSET_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_bits r v)

def _set_PMCNTEN_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_bits r v)

def _set_PMCR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_bits r v)

def _set_PMCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_bits r v)

def _set_PMDEVID_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMDEVID_Type_bits r v)

def _set_PMDEVTYPE_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMDEVTYPE_Type_bits r v)

def _set_PMECR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMECR_EL1_Type_bits r v)

def _set_PMEVCNTSVR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVCNTSVR_EL1_Type_bits r v)

def _set_PMEVTYPER_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_bits r v)

def _set_PMEVTYPER_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_Type_bits r v)

def _set_PMIAR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMIAR_EL1_Type_bits r v)

def _set_PMICFILTR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_bits r v)

def _set_PMICNTR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICNTR_EL0_Type_bits r v)

def _set_PMICNTSVR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICNTSVR_EL1_Type_bits r v)

def _set_PMIIDR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMIIDR_Type_bits r v)

def _set_PMINTENCLR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_bits r v)

def _set_PMINTENCLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_bits r v)

def _set_PMINTENSET_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_bits r v)

def _set_PMINTENSET_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_bits r v)

def _set_PMINTEN_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_bits r v)

def _set_PMITCTRL_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMITCTRL_Type_bits r v)

def _set_PMLAR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMLAR_Type_bits r v)

def _set_PMLSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMLSR_Type_bits r v)

def _set_PMMIR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_EL1_Type_bits r v)

def _set_PMMIR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_Type_bits r v)

def _set_PMOVSCLR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_bits r v)

def _set_PMOVSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_bits r v)

def _set_PMOVSSET_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_bits r v)

def _set_PMOVSSET_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_bits r v)

def _set_PMOVS_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_bits r v)

def _set_PMPCSCTL_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPCSCTL_Type_bits r v)

def _set_PMPCSR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPCSR_Type_bits r v)

def _set_PMPIDR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR0_Type_bits r v)

def _set_PMPIDR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR1_Type_bits r v)

def _set_PMPIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR2_Type_bits r v)

def _set_PMPIDR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR3_Type_bits r v)

def _set_PMPIDR4_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR4_Type_bits r v)

def _set_PMSCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL1_Type_bits r v)

def _set_PMSCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL2_Type_bits r v)

def _set_PMSDSFR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_bits r v)

def _set_PMSELR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSELR_EL0_Type_bits r v)

def _set_PMSELR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSELR_Type_bits r v)

def _set_PMSEVFR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_bits r v)

def _set_PMSFCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_bits r v)

def _set_PMSICR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSICR_EL1_Type_bits r v)

def _set_PMSIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_bits r v)

def _set_PMSIRR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIRR_EL1_Type_bits r v)

def _set_PMSLATFR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSLATFR_EL1_Type_bits r v)

def _set_PMSNEVFR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_bits r v)

def _set_PMSSCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSSCR_EL1_Type_bits r v)

def _set_PMSWINC_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_bits r v)

def _set_PMSWINC_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_bits r v)

def _set_PMUACR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_bits r v)

def _set_PMUSERENR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_bits r v)

def _set_PMUSERENR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_Type_bits r v)

def _set_PMVCIDSR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMVCIDSR_Type_bits r v)

def _set_PMVIDSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMVIDSR_Type_bits r v)

def _set_PMXEVCNTR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMXEVCNTR_EL0_Type_bits r v)

def _set_PMZR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_bits r v)

def _set_POR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_bits r v)

def _set_POR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_bits r v)

def _set_POR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_bits r v)

def _set_POR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_bits r v)

def _set_PRRR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_bits r v)

def _set_RCWMASK_EL1_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RCWMASK_EL1_Type_bits r v)

def _set_RCWSMASK_EL1_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RCWSMASK_EL1_Type_bits r v)

def _set_RGSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RGSR_EL1_Type_bits r v)

def _set_RMR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_EL1_Type_bits r v)

def _set_RMR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_EL2_Type_bits r v)

def _set_RMR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_EL3_Type_bits r v)

def _set_RMR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_Type_bits r v)

def _set_RNDRRS_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RNDRRS_Type_bits r v)

def _set_RNDR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RNDR_Type_bits r v)

def _set_RVBAR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVBAR_EL1_Type_bits r v)

def _set_RVBAR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVBAR_EL2_Type_bits r v)

def _set_RVBAR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVBAR_EL3_Type_bits r v)

def _set_S1PIRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_bits r v)

def _set_S1PORType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_bits r v)

def _set_S2PIRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_bits r v)

def _set_S2PIR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_bits r v)

def _set_S2POR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_bits r v)

def _set_SCRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_bits r v)

def _set_SCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_bits r v)

def _set_SCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_bits r v)

def _set_SCTLR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL1_Type_bits r v)

def _set_SCTLR2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_bits r v)

def _set_SCTLR2_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL3_Type_bits r v)

def _set_SCTLRType_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_bits r v)

def _set_SCTLR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_bits r v)

def _set_SCTLR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_bits r v)

def _set_SCTLR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_bits r v)

def _set_SCTLR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_bits r v)

def _set_SDCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDCR_Type_bits r v)

def _set_SDER32_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDER32_EL2_Type_bits r v)

def _set_SDER32_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDER32_EL3_Type_bits r v)

def _set_SDER_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDER_Type_bits r v)

def _set_SMCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL1_Type_bits r v)

def _set_SMCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL2_Type_bits r v)

def _set_SMCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL3_Type_bits r v)

def _set_SMIDR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMIDR_EL1_Type_bits r v)

def _set_SMPRIMAP_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_bits r v)

def _set_SMPRI_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRI_EL1_Type_bits r v)

def _set_SPMACCESSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_bits r v)

def _set_SPMACCESSR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_bits r v)

def _set_SPMACCESSR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_bits r v)

def _set_SPMSELR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMSELR_EL0_Type_bits r v)

def _set_SPSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_bits r v)

def _set_SPSR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_bits r v)

def _set_SPSR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_bits r v)

def _set_SPSR_abt_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_bits r v)

def _set_SPSR_fiq_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_bits r v)

def _set_SPSR_hyp_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_bits r v)

def _set_SPSR_irq_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_bits r v)

def _set_SPSR_mon_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_bits r v)

def _set_SPSR_svc_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_bits r v)

def _set_SPSR_und_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_bits r v)

def _set_TCR2_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_bits r v)

def _set_TCR2_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_bits r v)

def _set_TCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_bits r v)

def _set_TCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_bits r v)

def _set_TCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_bits r v)

def _set_TFSRE0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSRE0_EL1_Type_bits r v)

def _set_TFSR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSR_EL1_Type_bits r v)

def _set_TFSR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSR_EL2_Type_bits r v)

def _set_TFSR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSR_EL3_Type_bits r v)

def _set_TLBTR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TLBTR_Type_bits r v)

def _set_TRFCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_EL1_Type_bits r v)

def _set_TRFCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_EL2_Type_bits r v)

def _set_TRFCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_Type_bits r v)

def _set_TTBCR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_bits r v)

def _set_TTBCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_bits r v)

def _set_TTBR0_EL1_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL1_Type_bits r v)

def _set_TTBR0_EL2_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL2_Type_bits r v)

def _set_TTBR0_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL3_Type_bits r v)

def _set_TTBR0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_Type_bits r v)

def _set_TTBR1_EL1_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_EL1_Type_bits r v)

def _set_TTBR1_EL2_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_EL2_Type_bits r v)

def _set_TTBR1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_Type_bits r v)

def _set_VDFSR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDFSR_Type_bits r v)

def _set_VDISR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_EL2_Type_bits r v)

def _set_VDISR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_Type_bits r v)

def _set_VMECID_A_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMECID_A_EL2_Type_bits r v)

def _set_VMECID_P_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMECID_P_EL2_Type_bits r v)

def _set_VMPIDR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_bits r v)

def _set_VMPIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_Type_bits r v)

def _set_VNCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VNCR_EL2_Type_bits r v)

def _set_VPIDR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_EL2_Type_bits r v)

def _set_VPIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_Type_bits r v)

def _set_VSESR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSESR_EL2_Type_bits r v)

def _set_VSTCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSTCR_EL2_Type_bits r v)

def _set_VSTTBR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSTTBR_EL2_Type_bits r v)

def _set_VTCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_bits r v)

def _set_VTCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_bits r v)

def _set_VTTBR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTTBR_EL2_Type_bits r v)

def _set_VTTBR_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTTBR_Type_bits r v)

def _set_ZCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ZCR_EL1_Type_bits r v)

def _set_ZCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ZCR_EL2_Type_bits r v)

def _set_ZCR_EL3_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ZCR_EL3_Type_bits r v)

def _set_Configuration_Type_CFGEND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_CFGEND r v)

def _set_Configuration_Type_CONFIG64 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_CONFIG64 r v)

def _set_Configuration_Type_CfgNMFI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_CfgNMFI r v)

def _set_Configuration_Type_Cp15SDisable (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_Cp15SDisable r v)

def _set_Configuration_Type_Cp15SDisable2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_Cp15SDisable2 r v)

def _set_Configuration_Type_ExceptInit (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_ExceptInit r v)

def _set_Configuration_Type_HIVECS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_HIVECS r v)

def _set_Configuration_Type_RW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_RW r v)

def _set_HCR_EL2_Type_RW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_RW r v)

def _set_SCRType_RW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_RW r v)

def _set_SCR_EL3_Type_RW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_RW r v)

def _set_Configuration_Type_disableNIDebug (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_disableNIDebug r v)

def _set_Configuration_Type_disableSPIDebug (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_disableSPIDebug r v)

def _set_Configuration_Type_disableSPNIDebug (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_Configuration_Type_disableSPNIDebug r v)

def _set_DormantCtl_Type_Dbgnopwrdwn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_Dbgnopwrdwn r v)

def _set_DormantCtl_Type_PowerDownStatusSupport (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_PowerDownStatusSupport r v)

def _set_DormantCtl_Type_ResetCatchStatus (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_ResetCatchStatus r v)

def _set_DormantCtl_Type_TestResetCatch (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_TestResetCatch r v)

def _set_DormantCtl_Type_dbgpwrupreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_dbgpwrupreq r v)

def _set_DormantCtl_Type_dbgrstreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_dbgrstreq r v)

def _set_DormantCtl_Type_etmpwrdwnreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_etmpwrdwnreq r v)

def _set_DormantCtl_Type_etmpwrupreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_etmpwrupreq r v)

def _set_DormantCtl_Type_nDbgpwrdwnreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_nDbgpwrdwnreq r v)

def _set_DormantCtl_Type_nPU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_nPU r v)

def _set_DormantCtl_Type_standbywfe (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_standbywfe r v)

def _set_DormantCtl_Type_standbywfi (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DormantCtl_Type_standbywfi r v)

def InitVariantImplemented (_ : Unit) : SailM Unit := do
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v8Ap0) (← readReg v8Ap0_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v8Ap1) (← readReg v8Ap1_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v8Ap2) (← readReg v8Ap2_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v8Ap3) (← readReg v8Ap3_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v8Ap4) (← readReg v8Ap4_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v8Ap5) (← readReg v8Ap5_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v8Ap6) (← readReg v8Ap6_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v8Ap7) (← readReg v8Ap7_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v8Ap8) (← readReg v8Ap8_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v8Ap9) (← readReg v8Ap9_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v9Ap0) (← readReg v9Ap0_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v9Ap1) (← readReg v9Ap1_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v9Ap2) (← readReg v9Ap2_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v9Ap3) (← readReg v9Ap3_IMPLEMENTED))
  writeReg VariantImplemented (vectorUpdate (← readReg VariantImplemented) (num_of_ArchVersion v9Ap4) (← readReg v9Ap4_IMPLEMENTED))

def _set_SCRType_AW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_AW r v)

def _set_SCR_Type_AW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_AW r v)

def _set_SCRType_EA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_EA r v)

def _set_DISR_EL1_Type_EA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_EL1_Type_EA r v)

def _set_DISR_Type_EA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_Type_EA r v)

def _set_LOREA_EL1_Type_EA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 40)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LOREA_EL1_Type_EA r v)

def _set_PMBIDR_EL1_Type_EA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBIDR_EL1_Type_EA r v)

def _set_PMBSR_EL1_Type_EA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBSR_EL1_Type_EA r v)

def _set_SCR_EL3_Type_EA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_EA r v)

def _set_SCR_Type_EA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_EA r v)

def _set_SCRType_FIQ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_FIQ r v)

def _set_SCR_EL3_Type_FIQ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_FIQ r v)

def _set_SCR_Type_FIQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_FIQ r v)

def _set_SCRType_FW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_FW r v)

def _set_SCR_Type_FW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_FW r v)

def _set_SCRType_HCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_HCE r v)

def _set_SCR_EL3_Type_HCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_HCE r v)

def _set_SCR_Type_HCE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_HCE r v)

def _set_SCRType_IRQ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_IRQ r v)

def _set_SCR_EL3_Type_IRQ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_IRQ r v)

def _set_SCR_Type_IRQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_IRQ r v)

def _set_SCRType_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_NS r v)

def _set_DBGDSCRext_Type_NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_NS r v)

def _set_DBGDSCRint_Type_NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRint_Type_NS r v)

def _set_EDPCSR_Type_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPCSR_Type_NS r v)

def _set_EDVIDSR_Type_NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDVIDSR_Type_NS r v)

def _set_HPFAR_EL2_Type_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HPFAR_EL2_Type_NS r v)

def _set_MFAR_EL3_Type_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MFAR_EL3_Type_NS r v)

def _set_PAR_EL1_Type_NS (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_NS r v)

def _set_PAR_Type_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_NS r v)

def _set_PFAR_EL1_Type_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PFAR_EL1_Type_NS r v)

def _set_PFAR_EL2_Type_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PFAR_EL2_Type_NS r v)

def _set_PMPCSR_Type_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPCSR_Type_NS r v)

def _set_SCR_EL3_Type_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_NS r v)

def _set_SCR_Type_NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_NS r v)

def _set_SCRType_SCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_SCD r v)

def _set_SCR_Type_SCD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_SCD r v)

def _set_SCRType_SIF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_SIF r v)

def _set_SCR_EL3_Type_SIF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_SIF r v)

def _set_SCR_Type_SIF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_SIF r v)

def _set_SCRType_SMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_SMD r v)

def _set_SCR_EL3_Type_SMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_SMD r v)

def _set_SCRType_ST (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_ST r v)

def _set_ID_AA64MMFR2_EL1_Type_ST (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_ST r v)

def _set_PMSFCR_EL1_Type_ST (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_ST r v)

def _set_SCR_EL3_Type_ST (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_ST r v)

def _set_SCRType_TWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_TWE r v)

def _set_HCR_EL2_Type_TWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TWE r v)

def _set_HCR_Type_TWE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TWE r v)

def _set_SCR_EL3_Type_TWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TWE r v)

def _set_SCR_Type_TWE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_TWE r v)

def _set_SCRType_TWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_TWI r v)

def _set_HCR_EL2_Type_TWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TWI r v)

def _set_HCR_Type_TWI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TWI r v)

def _set_SCR_EL3_Type_TWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TWI r v)

def _set_SCR_Type_TWI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_TWI r v)

def _set_SCRType_nET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCRType_nET r v)

def _set_SCR_Type_nET (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_nET r v)

def _set_SCTLRType_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_A r v)

def _set_DISR_EL1_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_EL1_Type_A r v)

def _set_DISR_Type_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_Type_A r v)

def _set_DSPSR_EL0_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_A r v)

def _set_DSPSR_Type_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_A r v)

def _set_EDSCR_Type_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_A r v)

def _set_HSCTLR_Type_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_A r v)

def _set_ISR_EL1_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ISR_EL1_Type_A r v)

def _set_ISR_Type_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ISR_Type_A r v)

def _set_SCTLR_EL1_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_A r v)

def _set_SCTLR_EL2_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_A r v)

def _set_SCTLR_EL3_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_A r v)

def _set_SCTLR_Type_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_A r v)

def _set_SPSR_EL1_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_A r v)

def _set_SPSR_EL2_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_A r v)

def _set_SPSR_EL3_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_A r v)

def _set_SPSR_abt_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_A r v)

def _set_SPSR_fiq_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_A r v)

def _set_SPSR_hyp_Type_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_A r v)

def _set_SPSR_irq_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_A r v)

def _set_SPSR_mon_Type_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_A r v)

def _set_SPSR_svc_Type_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_A r v)

def _set_SPSR_und_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_A r v)

def _set_VDISR_EL2_Type_A (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_EL2_Type_A r v)

def _set_VDISR_Type_A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_Type_A r v)

def _set_SCTLRType_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_C r v)

def _set_DSPSR_EL0_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_C r v)

def _set_DSPSR_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_C r v)

def _set_FPSCR_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_C r v)

def _set_FPSR_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_C r v)

def _set_HSCTLR_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_C r v)

def _set_PMCNTENCLR_EL0_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_C r v)

def _set_PMCNTENCLR_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_C r v)

def _set_PMCNTENSET_EL0_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_C r v)

def _set_PMCNTENSET_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_C r v)

def _set_PMCNTEN_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_C r v)

def _set_PMCR_EL0_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_C r v)

def _set_PMCR_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_C r v)

def _set_PMINTENCLR_EL1_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_C r v)

def _set_PMINTENCLR_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_C r v)

def _set_PMINTENSET_EL1_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_C r v)

def _set_PMINTENSET_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_C r v)

def _set_PMINTEN_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_C r v)

def _set_PMOVSCLR_EL0_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_C r v)

def _set_PMOVSSET_EL0_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_C r v)

def _set_PMOVS_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_C r v)

def _set_PMUACR_EL1_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_C r v)

def _set_PMZR_EL0_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_C r v)

def _set_SCTLR_EL1_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_C r v)

def _set_SCTLR_EL2_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_C r v)

def _set_SCTLR_EL3_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_C r v)

def _set_SCTLR_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_C r v)

def _set_SPSR_EL1_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_C r v)

def _set_SPSR_EL2_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_C r v)

def _set_SPSR_EL3_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_C r v)

def _set_SPSR_abt_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_C r v)

def _set_SPSR_fiq_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_C r v)

def _set_SPSR_hyp_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_C r v)

def _set_SPSR_irq_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_C r v)

def _set_SPSR_mon_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_C r v)

def _set_SPSR_svc_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_C r v)

def _set_SPSR_und_Type_C (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_C r v)

def _set_SCTLRType_CP15BEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_CP15BEN r v)

def _set_HSCTLR_Type_CP15BEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_CP15BEN r v)

def _set_SCTLR_EL1_Type_CP15BEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_CP15BEN r v)

def _set_SCTLR_EL2_Type_CP15BEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_CP15BEN r v)

def _set_SCTLR_Type_CP15BEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_CP15BEN r v)

def _set_SCTLRType_DSSBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_DSSBS r v)

def _set_HSCTLR_Type_DSSBS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_DSSBS r v)

def _set_SCTLR_EL1_Type_DSSBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_DSSBS r v)

def _set_SCTLR_EL2_Type_DSSBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_DSSBS r v)

def _set_SCTLR_EL3_Type_DSSBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_DSSBS r v)

def _set_SCTLR_Type_DSSBS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_DSSBS r v)

def _set_SCTLRType_DZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_DZE r v)

def _set_FPCRType_DZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_DZE r v)

def _set_FPCR_Type_DZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_DZE r v)

def _set_FPSCR_Type_DZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_DZE r v)

def _set_SCTLR_EL1_Type_DZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_DZE r v)

def _set_SCTLR_EL2_Type_DZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_DZE r v)

def _set_SCTLRType_E0E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_E0E r v)

def _set_SCTLR_EL1_Type_E0E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_E0E r v)

def _set_SCTLR_EL2_Type_E0E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_E0E r v)

def _set_SCTLRType_EE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_EE r v)

def _set_HSCTLR_Type_EE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_EE r v)

def _set_SCTLR_EL1_Type_EE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EE r v)

def _set_SCTLR_EL2_Type_EE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EE r v)

def _set_SCTLR_EL3_Type_EE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EE r v)

def _set_SCTLR_Type_EE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_EE r v)

def _set_SCTLRType_EPAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_EPAN r v)

def _set_SCTLR_EL1_Type_EPAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EPAN r v)

def _set_SCTLR_EL2_Type_EPAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EPAN r v)

def _set_SCTLRType_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_I r v)

def _set_DBGVCR32_EL2_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_I r v)

def _set_DBGVCR_Type_I (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_I r v)

def _set_DSPSR_EL0_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_I r v)

def _set_DSPSR_Type_I (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_I r v)

def _set_HSCTLR_Type_I (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_I r v)

def _set_ISR_EL1_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ISR_EL1_Type_I r v)

def _set_ISR_Type_I (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ISR_Type_I r v)

def _set_SCTLR_EL1_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_I r v)

def _set_SCTLR_EL2_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_I r v)

def _set_SCTLR_EL3_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_I r v)

def _set_SCTLR_Type_I (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_I r v)

def _set_SPSR_EL1_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_I r v)

def _set_SPSR_EL2_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_I r v)

def _set_SPSR_EL3_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_I r v)

def _set_SPSR_abt_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_I r v)

def _set_SPSR_fiq_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_I r v)

def _set_SPSR_hyp_Type_I (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_I r v)

def _set_SPSR_irq_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_I r v)

def _set_SPSR_mon_Type_I (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_I r v)

def _set_SPSR_svc_Type_I (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_I r v)

def _set_SPSR_und_Type_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_I r v)

def _set_SCTLRType_IESB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_IESB r v)

def _set_ID_AA64MMFR2_EL1_Type_IESB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_IESB r v)

def _set_SCTLR_EL1_Type_IESB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_IESB r v)

def _set_SCTLR_EL2_Type_IESB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_IESB r v)

def _set_SCTLR_EL3_Type_IESB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_IESB r v)

def _set_SCTLRType_ITD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_ITD r v)

def _set_HSCTLR_Type_ITD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_ITD r v)

def _set_SCTLR_EL1_Type_ITD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_ITD r v)

def _set_SCTLR_EL2_Type_ITD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_ITD r v)

def _set_SCTLR_Type_ITD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_ITD r v)

def _set_SCTLRType_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_M r v)

def _set_DSPSR_Type_M (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_M r v)

def _set_HSCTLR_Type_M (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_M r v)

def _set_MPIDR_Type_M (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_Type_M r v)

def _set_PMCCFILTR_EL0_Type_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_M r v)

def _set_PMEVTYPER_EL0_Type_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_M r v)

def _set_PMICFILTR_EL0_Type_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_M r v)

def _set_SCTLR_EL1_Type_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_M r v)

def _set_SCTLR_EL2_Type_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_M r v)

def _set_SCTLR_EL3_Type_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_M r v)

def _set_SCTLR_Type_M (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_M r v)

def _set_SPSR_abt_Type_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_M r v)

def _set_SPSR_fiq_Type_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_M r v)

def _set_SPSR_hyp_Type_M (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_M r v)

def _set_SPSR_irq_Type_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_M r v)

def _set_SPSR_mon_Type_M (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_M r v)

def _set_SPSR_svc_Type_M (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_M r v)

def _set_SPSR_und_Type_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_M r v)

def _set_VMPIDR_Type_M (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_Type_M r v)

def _set_SCTLRType_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_NMI r v)

def _set_GICD_TYPER_Type_NMI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_NMI r v)

def _set_ICC_AP1R_EL1_Type_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_AP1R_EL1_Type_NMI r v)

def _set_ICC_RPR_EL1_Type_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_RPR_EL1_Type_NMI r v)

def _set_ICH_AP1R_EL2_Type_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_NMI r v)

def _set_ICH_LR_EL2_Type_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_NMI r v)

def _set_ICV_AP1R_EL1_Type_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_AP1R_EL1_Type_NMI r v)

def _set_ICV_RPR_EL1_Type_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_RPR_EL1_Type_NMI r v)

def _set_ID_AA64PFR1_EL1_Type_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_NMI r v)

def _set_SCTLR_EL1_Type_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_NMI r v)

def _set_SCTLR_EL2_Type_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_NMI r v)

def _set_SCTLR_EL3_Type_NMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_NMI r v)

def _set_SCTLRType_SA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_SA r v)

def _set_LORSA_EL1_Type_SA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 40)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORSA_EL1_Type_SA r v)

def _set_SCTLR_EL1_Type_SA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_SA r v)

def _set_SCTLR_EL2_Type_SA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_SA r v)

def _set_SCTLR_EL3_Type_SA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_SA r v)

def _set_VSTCR_EL2_Type_SA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSTCR_EL2_Type_SA r v)

def _set_SCTLRType_SA0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_SA0 r v)

def _set_SCTLR_EL1_Type_SA0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_SA0 r v)

def _set_SCTLR_EL2_Type_SA0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_SA0 r v)

def _set_SCTLRType_SED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_SED r v)

def _set_HSCTLR_Type_SED (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_SED r v)

def _set_SCTLR_EL1_Type_SED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_SED r v)

def _set_SCTLR_EL2_Type_SED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_SED r v)

def _set_SCTLR_Type_SED (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_SED r v)

def _set_SCTLRType_SPAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_SPAN r v)

def _set_SCTLR_EL1_Type_SPAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_SPAN r v)

def _set_SCTLR_EL2_Type_SPAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_SPAN r v)

def _set_SCTLR_Type_SPAN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_SPAN r v)

def _set_SCTLRType_SPINTMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_SPINTMASK r v)

def _set_SCTLR_EL1_Type_SPINTMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_SPINTMASK r v)

def _set_SCTLR_EL2_Type_SPINTMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_SPINTMASK r v)

def _set_SCTLR_EL3_Type_SPINTMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_SPINTMASK r v)

def _set_SCTLRType_TIDCP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_TIDCP r v)

def _set_HCR_EL2_Type_TIDCP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TIDCP r v)

def _set_HCR_Type_TIDCP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TIDCP r v)

def _set_SCTLR_EL1_Type_TIDCP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TIDCP r v)

def _set_SCTLR_EL2_Type_TIDCP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TIDCP r v)

def _set_SCTLRType_TME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_TME r v)

def _set_HCR_EL2_Type_TME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TME r v)

def _set_ID_AA64ISAR0_EL1_Type_TME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_TME r v)

def _set_SCR_EL3_Type_TME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TME r v)

def _set_SCTLR_EL1_Type_TME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TME r v)

def _set_SCTLR_EL2_Type_TME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TME r v)

def _set_SCTLR_EL3_Type_TME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_TME r v)

def _set_SCTLRType_TME0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_TME0 r v)

def _set_SCTLR_EL1_Type_TME0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TME0 r v)

def _set_SCTLR_EL2_Type_TME0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TME0 r v)

def _set_SCTLRType_TMT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_TMT r v)

def _set_SCTLR_EL1_Type_TMT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TMT r v)

def _set_SCTLR_EL2_Type_TMT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TMT r v)

def _set_SCTLR_EL3_Type_TMT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_TMT r v)

def _set_SCTLRType_TMT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_TMT0 r v)

def _set_SCTLR_EL1_Type_TMT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TMT0 r v)

def _set_SCTLR_EL2_Type_TMT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TMT0 r v)

def _set_SCTLRType_TSCXT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_TSCXT r v)

def _set_SCTLR_EL1_Type_TSCXT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TSCXT r v)

def _set_SCTLR_EL2_Type_TSCXT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TSCXT r v)

def _set_SCTLRType_UCI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_UCI r v)

def _set_SCTLR_EL1_Type_UCI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_UCI r v)

def _set_SCTLR_EL2_Type_UCI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_UCI r v)

def _set_SCTLRType_UCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_UCT r v)

def _set_SCTLR_EL1_Type_UCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_UCT r v)

def _set_SCTLR_EL2_Type_UCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_UCT r v)

def _set_SCTLRType_UMA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_UMA r v)

def _set_SCTLR_EL1_Type_UMA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_UMA r v)

def _set_SCTLRType_WXN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_WXN r v)

def _set_HSCTLR_Type_WXN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_WXN r v)

def _set_SCTLR_EL1_Type_WXN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_WXN r v)

def _set_SCTLR_EL2_Type_WXN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_WXN r v)

def _set_SCTLR_EL3_Type_WXN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_WXN r v)

def _set_SCTLR_Type_WXN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_WXN r v)

def _set_SCTLRType_nAA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_nAA r v)

def _set_SCTLR_EL1_Type_nAA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_nAA r v)

def _set_SCTLR_EL2_Type_nAA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_nAA r v)

def _set_SCTLR_EL3_Type_nAA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_nAA r v)

def _set_SCTLRType_nTWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_nTWE r v)

def _set_SCTLR_EL1_Type_nTWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_nTWE r v)

def _set_SCTLR_EL2_Type_nTWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_nTWE r v)

def _set_SCTLR_Type_nTWE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_nTWE r v)

def _set_SCTLRType_nTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLRType_nTWI r v)

def _set_SCTLR_EL1_Type_nTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_nTWI r v)

def _set_SCTLR_EL2_Type_nTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_nTWI r v)

def _set_SCTLR_Type_nTWI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_nTWI r v)

def _set_MAIRType_Attr0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIRType_Attr0 r v)

def _set_HMAIR0_Type_Attr0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HMAIR0_Type_Attr0 r v)

def _set_MAIR0_Type_Attr0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR0_Type_Attr0 r v)

def _set_MAIR2_EL1_Type_Attr0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL1_Type_Attr0 r v)

def _set_MAIR2_EL2_Type_Attr0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL2_Type_Attr0 r v)

def _set_MAIR2_EL3_Type_Attr0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL3_Type_Attr0 r v)

def _set_MAIR_EL1_Type_Attr0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL1_Type_Attr0 r v)

def _set_MAIR_EL2_Type_Attr0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL2_Type_Attr0 r v)

def _set_MAIR_EL3_Type_Attr0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL3_Type_Attr0 r v)

def _set_MAIRType_Attr1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIRType_Attr1 r v)

def _set_HMAIR0_Type_Attr1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HMAIR0_Type_Attr1 r v)

def _set_MAIR0_Type_Attr1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR0_Type_Attr1 r v)

def _set_MAIR2_EL1_Type_Attr1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL1_Type_Attr1 r v)

def _set_MAIR2_EL2_Type_Attr1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL2_Type_Attr1 r v)

def _set_MAIR2_EL3_Type_Attr1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL3_Type_Attr1 r v)

def _set_MAIR_EL1_Type_Attr1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL1_Type_Attr1 r v)

def _set_MAIR_EL2_Type_Attr1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL2_Type_Attr1 r v)

def _set_MAIR_EL3_Type_Attr1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL3_Type_Attr1 r v)

def _set_MAIRType_Attr2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIRType_Attr2 r v)

def _set_HMAIR0_Type_Attr2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HMAIR0_Type_Attr2 r v)

def _set_MAIR0_Type_Attr2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR0_Type_Attr2 r v)

def _set_MAIR2_EL1_Type_Attr2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL1_Type_Attr2 r v)

def _set_MAIR2_EL2_Type_Attr2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL2_Type_Attr2 r v)

def _set_MAIR2_EL3_Type_Attr2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL3_Type_Attr2 r v)

def _set_MAIR_EL1_Type_Attr2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL1_Type_Attr2 r v)

def _set_MAIR_EL2_Type_Attr2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL2_Type_Attr2 r v)

def _set_MAIR_EL3_Type_Attr2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL3_Type_Attr2 r v)

def _set_MAIRType_Attr3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIRType_Attr3 r v)

def _set_HMAIR0_Type_Attr3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HMAIR0_Type_Attr3 r v)

def _set_MAIR0_Type_Attr3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR0_Type_Attr3 r v)

def _set_MAIR2_EL1_Type_Attr3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL1_Type_Attr3 r v)

def _set_MAIR2_EL2_Type_Attr3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL2_Type_Attr3 r v)

def _set_MAIR2_EL3_Type_Attr3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL3_Type_Attr3 r v)

def _set_MAIR_EL1_Type_Attr3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL1_Type_Attr3 r v)

def _set_MAIR_EL2_Type_Attr3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL2_Type_Attr3 r v)

def _set_MAIR_EL3_Type_Attr3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL3_Type_Attr3 r v)

def _set_MAIRType_Attr4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIRType_Attr4 r v)

def _set_HMAIR1_Type_Attr4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HMAIR1_Type_Attr4 r v)

def _set_MAIR1_Type_Attr4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR1_Type_Attr4 r v)

def _set_MAIR2_EL1_Type_Attr4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL1_Type_Attr4 r v)

def _set_MAIR2_EL2_Type_Attr4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL2_Type_Attr4 r v)

def _set_MAIR2_EL3_Type_Attr4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL3_Type_Attr4 r v)

def _set_MAIR_EL1_Type_Attr4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL1_Type_Attr4 r v)

def _set_MAIR_EL2_Type_Attr4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL2_Type_Attr4 r v)

def _set_MAIR_EL3_Type_Attr4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL3_Type_Attr4 r v)

def _set_MAIRType_Attr5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIRType_Attr5 r v)

def _set_HMAIR1_Type_Attr5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HMAIR1_Type_Attr5 r v)

def _set_MAIR1_Type_Attr5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR1_Type_Attr5 r v)

def _set_MAIR2_EL1_Type_Attr5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL1_Type_Attr5 r v)

def _set_MAIR2_EL2_Type_Attr5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL2_Type_Attr5 r v)

def _set_MAIR2_EL3_Type_Attr5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL3_Type_Attr5 r v)

def _set_MAIR_EL1_Type_Attr5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL1_Type_Attr5 r v)

def _set_MAIR_EL2_Type_Attr5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL2_Type_Attr5 r v)

def _set_MAIR_EL3_Type_Attr5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL3_Type_Attr5 r v)

def _set_MAIRType_Attr6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIRType_Attr6 r v)

def _set_HMAIR1_Type_Attr6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HMAIR1_Type_Attr6 r v)

def _set_MAIR1_Type_Attr6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR1_Type_Attr6 r v)

def _set_MAIR2_EL1_Type_Attr6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL1_Type_Attr6 r v)

def _set_MAIR2_EL2_Type_Attr6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL2_Type_Attr6 r v)

def _set_MAIR2_EL3_Type_Attr6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL3_Type_Attr6 r v)

def _set_MAIR_EL1_Type_Attr6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL1_Type_Attr6 r v)

def _set_MAIR_EL2_Type_Attr6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL2_Type_Attr6 r v)

def _set_MAIR_EL3_Type_Attr6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL3_Type_Attr6 r v)

def _set_MAIRType_Attr7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIRType_Attr7 r v)

def _set_HMAIR1_Type_Attr7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HMAIR1_Type_Attr7 r v)

def _set_MAIR1_Type_Attr7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR1_Type_Attr7 r v)

def _set_MAIR2_EL1_Type_Attr7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL1_Type_Attr7 r v)

def _set_MAIR2_EL2_Type_Attr7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL2_Type_Attr7 r v)

def _set_MAIR2_EL3_Type_Attr7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR2_EL3_Type_Attr7 r v)

def _set_MAIR_EL1_Type_Attr7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL1_Type_Attr7 r v)

def _set_MAIR_EL2_Type_Attr7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL2_Type_Attr7 r v)

def _set_MAIR_EL3_Type_Attr7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MAIR_EL3_Type_Attr7 r v)

def _set_S1PIRType_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm0 r v)

def _set_PIRE0_EL1_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm0 r v)

def _set_PIRE0_EL2_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm0 r v)

def _set_PIR_EL1_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm0 r v)

def _set_PIR_EL2_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm0 r v)

def _set_PIR_EL3_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm0 r v)

def _set_POR_EL0_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm0 r v)

def _set_POR_EL1_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm0 r v)

def _set_POR_EL2_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm0 r v)

def _set_POR_EL3_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm0 r v)

def _set_S1PORType_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm0 r v)

def _set_S2PIRType_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm0 r v)

def _set_S2PIR_EL2_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm0 r v)

def _set_S2POR_EL1_Type_Perm0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm0 r v)

def _set_S1PIRType_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm1 r v)

def _set_PIRE0_EL1_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm1 r v)

def _set_PIRE0_EL2_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm1 r v)

def _set_PIR_EL1_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm1 r v)

def _set_PIR_EL2_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm1 r v)

def _set_PIR_EL3_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm1 r v)

def _set_POR_EL0_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm1 r v)

def _set_POR_EL1_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm1 r v)

def _set_POR_EL2_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm1 r v)

def _set_POR_EL3_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm1 r v)

def _set_S1PORType_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm1 r v)

def _set_S2PIRType_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm1 r v)

def _set_S2PIR_EL2_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm1 r v)

def _set_S2POR_EL1_Type_Perm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm1 r v)

def _set_S1PIRType_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm10 r v)

def _set_PIRE0_EL1_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm10 r v)

def _set_PIRE0_EL2_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm10 r v)

def _set_PIR_EL1_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm10 r v)

def _set_PIR_EL2_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm10 r v)

def _set_PIR_EL3_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm10 r v)

def _set_POR_EL0_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm10 r v)

def _set_POR_EL1_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm10 r v)

def _set_POR_EL2_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm10 r v)

def _set_POR_EL3_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm10 r v)

def _set_S1PORType_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm10 r v)

def _set_S2PIRType_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm10 r v)

def _set_S2PIR_EL2_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm10 r v)

def _set_S2POR_EL1_Type_Perm10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm10 r v)

def _set_S1PIRType_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm11 r v)

def _set_PIRE0_EL1_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm11 r v)

def _set_PIRE0_EL2_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm11 r v)

def _set_PIR_EL1_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm11 r v)

def _set_PIR_EL2_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm11 r v)

def _set_PIR_EL3_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm11 r v)

def _set_POR_EL0_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm11 r v)

def _set_POR_EL1_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm11 r v)

def _set_POR_EL2_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm11 r v)

def _set_POR_EL3_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm11 r v)

def _set_S1PORType_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm11 r v)

def _set_S2PIRType_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm11 r v)

def _set_S2PIR_EL2_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm11 r v)

def _set_S2POR_EL1_Type_Perm11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm11 r v)

def _set_S1PIRType_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm12 r v)

def _set_PIRE0_EL1_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm12 r v)

def _set_PIRE0_EL2_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm12 r v)

def _set_PIR_EL1_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm12 r v)

def _set_PIR_EL2_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm12 r v)

def _set_PIR_EL3_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm12 r v)

def _set_POR_EL0_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm12 r v)

def _set_POR_EL1_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm12 r v)

def _set_POR_EL2_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm12 r v)

def _set_POR_EL3_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm12 r v)

def _set_S1PORType_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm12 r v)

def _set_S2PIRType_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm12 r v)

def _set_S2PIR_EL2_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm12 r v)

def _set_S2POR_EL1_Type_Perm12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm12 r v)

def _set_S1PIRType_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm13 r v)

def _set_PIRE0_EL1_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm13 r v)

def _set_PIRE0_EL2_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm13 r v)

def _set_PIR_EL1_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm13 r v)

def _set_PIR_EL2_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm13 r v)

def _set_PIR_EL3_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm13 r v)

def _set_POR_EL0_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm13 r v)

def _set_POR_EL1_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm13 r v)

def _set_POR_EL2_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm13 r v)

def _set_POR_EL3_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm13 r v)

def _set_S1PORType_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm13 r v)

def _set_S2PIRType_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm13 r v)

def _set_S2PIR_EL2_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm13 r v)

def _set_S2POR_EL1_Type_Perm13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm13 r v)

def _set_S1PIRType_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm14 r v)

def _set_PIRE0_EL1_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm14 r v)

def _set_PIRE0_EL2_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm14 r v)

def _set_PIR_EL1_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm14 r v)

def _set_PIR_EL2_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm14 r v)

def _set_PIR_EL3_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm14 r v)

def _set_POR_EL0_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm14 r v)

def _set_POR_EL1_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm14 r v)

def _set_POR_EL2_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm14 r v)

def _set_POR_EL3_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm14 r v)

def _set_S1PORType_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm14 r v)

def _set_S2PIRType_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm14 r v)

def _set_S2PIR_EL2_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm14 r v)

def _set_S2POR_EL1_Type_Perm14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm14 r v)

def _set_S1PIRType_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm15 r v)

def _set_PIRE0_EL1_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm15 r v)

def _set_PIRE0_EL2_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm15 r v)

def _set_PIR_EL1_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm15 r v)

def _set_PIR_EL2_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm15 r v)

def _set_PIR_EL3_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm15 r v)

def _set_POR_EL0_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm15 r v)

def _set_POR_EL1_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm15 r v)

def _set_POR_EL2_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm15 r v)

def _set_POR_EL3_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm15 r v)

def _set_S1PORType_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm15 r v)

def _set_S2PIRType_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm15 r v)

def _set_S2PIR_EL2_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm15 r v)

def _set_S2POR_EL1_Type_Perm15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm15 r v)

def _set_S1PIRType_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm2 r v)

def _set_PIRE0_EL1_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm2 r v)

def _set_PIRE0_EL2_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm2 r v)

def _set_PIR_EL1_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm2 r v)

def _set_PIR_EL2_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm2 r v)

def _set_PIR_EL3_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm2 r v)

def _set_POR_EL0_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm2 r v)

def _set_POR_EL1_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm2 r v)

def _set_POR_EL2_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm2 r v)

def _set_POR_EL3_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm2 r v)

def _set_S1PORType_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm2 r v)

def _set_S2PIRType_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm2 r v)

def _set_S2PIR_EL2_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm2 r v)

def _set_S2POR_EL1_Type_Perm2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm2 r v)

def _set_S1PIRType_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm3 r v)

def _set_PIRE0_EL1_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm3 r v)

def _set_PIRE0_EL2_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm3 r v)

def _set_PIR_EL1_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm3 r v)

def _set_PIR_EL2_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm3 r v)

def _set_PIR_EL3_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm3 r v)

def _set_POR_EL0_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm3 r v)

def _set_POR_EL1_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm3 r v)

def _set_POR_EL2_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm3 r v)

def _set_POR_EL3_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm3 r v)

def _set_S1PORType_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm3 r v)

def _set_S2PIRType_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm3 r v)

def _set_S2PIR_EL2_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm3 r v)

def _set_S2POR_EL1_Type_Perm3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm3 r v)

def _set_S1PIRType_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm4 r v)

def _set_PIRE0_EL1_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm4 r v)

def _set_PIRE0_EL2_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm4 r v)

def _set_PIR_EL1_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm4 r v)

def _set_PIR_EL2_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm4 r v)

def _set_PIR_EL3_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm4 r v)

def _set_POR_EL0_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm4 r v)

def _set_POR_EL1_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm4 r v)

def _set_POR_EL2_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm4 r v)

def _set_POR_EL3_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm4 r v)

def _set_S1PORType_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm4 r v)

def _set_S2PIRType_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm4 r v)

def _set_S2PIR_EL2_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm4 r v)

def _set_S2POR_EL1_Type_Perm4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm4 r v)

def _set_S1PIRType_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm5 r v)

def _set_PIRE0_EL1_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm5 r v)

def _set_PIRE0_EL2_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm5 r v)

def _set_PIR_EL1_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm5 r v)

def _set_PIR_EL2_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm5 r v)

def _set_PIR_EL3_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm5 r v)

def _set_POR_EL0_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm5 r v)

def _set_POR_EL1_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm5 r v)

def _set_POR_EL2_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm5 r v)

def _set_POR_EL3_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm5 r v)

def _set_S1PORType_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm5 r v)

def _set_S2PIRType_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm5 r v)

def _set_S2PIR_EL2_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm5 r v)

def _set_S2POR_EL1_Type_Perm5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm5 r v)

def _set_S1PIRType_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm6 r v)

def _set_PIRE0_EL1_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm6 r v)

def _set_PIRE0_EL2_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm6 r v)

def _set_PIR_EL1_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm6 r v)

def _set_PIR_EL2_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm6 r v)

def _set_PIR_EL3_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm6 r v)

def _set_POR_EL0_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm6 r v)

def _set_POR_EL1_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm6 r v)

def _set_POR_EL2_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm6 r v)

def _set_POR_EL3_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm6 r v)

def _set_S1PORType_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm6 r v)

def _set_S2PIRType_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm6 r v)

def _set_S2PIR_EL2_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm6 r v)

def _set_S2POR_EL1_Type_Perm6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm6 r v)

def _set_S1PIRType_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm7 r v)

def _set_PIRE0_EL1_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm7 r v)

def _set_PIRE0_EL2_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm7 r v)

def _set_PIR_EL1_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm7 r v)

def _set_PIR_EL2_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm7 r v)

def _set_PIR_EL3_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm7 r v)

def _set_POR_EL0_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm7 r v)

def _set_POR_EL1_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm7 r v)

def _set_POR_EL2_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm7 r v)

def _set_POR_EL3_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm7 r v)

def _set_S1PORType_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm7 r v)

def _set_S2PIRType_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm7 r v)

def _set_S2PIR_EL2_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm7 r v)

def _set_S2POR_EL1_Type_Perm7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm7 r v)

def _set_S1PIRType_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm8 r v)

def _set_PIRE0_EL1_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm8 r v)

def _set_PIRE0_EL2_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm8 r v)

def _set_PIR_EL1_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm8 r v)

def _set_PIR_EL2_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm8 r v)

def _set_PIR_EL3_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm8 r v)

def _set_POR_EL0_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm8 r v)

def _set_POR_EL1_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm8 r v)

def _set_POR_EL2_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm8 r v)

def _set_POR_EL3_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm8 r v)

def _set_S1PORType_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm8 r v)

def _set_S2PIRType_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm8 r v)

def _set_S2PIR_EL2_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm8 r v)

def _set_S2POR_EL1_Type_Perm8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm8 r v)

def _set_S1PIRType_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PIRType_Perm9 r v)

def _set_PIRE0_EL1_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL1_Type_Perm9 r v)

def _set_PIRE0_EL2_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIRE0_EL2_Type_Perm9 r v)

def _set_PIR_EL1_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL1_Type_Perm9 r v)

def _set_PIR_EL2_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL2_Type_Perm9 r v)

def _set_PIR_EL3_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PIR_EL3_Type_Perm9 r v)

def _set_POR_EL0_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL0_Type_Perm9 r v)

def _set_POR_EL1_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL1_Type_Perm9 r v)

def _set_POR_EL2_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL2_Type_Perm9 r v)

def _set_POR_EL3_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_POR_EL3_Type_Perm9 r v)

def _set_S1PORType_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S1PORType_Perm9 r v)

def _set_S2PIRType_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIRType_Perm9 r v)

def _set_S2PIR_EL2_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2PIR_EL2_Type_Perm9 r v)

def _set_S2POR_EL1_Type_Perm9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_S2POR_EL1_Type_Perm9 r v)

def _set_ESRType_EC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESRType_EC r v)

def _set_EDESR_Type_EC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDESR_Type_EC r v)

def _set_ESR_EL1_Type_EC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL1_Type_EC r v)

def _set_ESR_EL2_Type_EC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL2_Type_EC r v)

def _set_ESR_EL3_Type_EC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL3_Type_EC r v)

def _set_HSR_Type_EC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSR_Type_EC r v)

def _set_PMBSR_EL1_Type_EC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBSR_EL1_Type_EC r v)

def _set_ESRType_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESRType_IL r v)

def _set_DSPSR_EL0_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_IL r v)

def _set_DSPSR_Type_IL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_IL r v)

def _set_ESR_EL1_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL1_Type_IL r v)

def _set_ESR_EL2_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL2_Type_IL r v)

def _set_ESR_EL3_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL3_Type_IL r v)

def _set_HSR_Type_IL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSR_Type_IL r v)

def _set_SPSR_EL1_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_IL r v)

def _set_SPSR_EL2_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_IL r v)

def _set_SPSR_EL3_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_IL r v)

def _set_SPSR_abt_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_IL r v)

def _set_SPSR_fiq_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_IL r v)

def _set_SPSR_hyp_Type_IL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_IL r v)

def _set_SPSR_irq_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_IL r v)

def _set_SPSR_mon_Type_IL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_IL r v)

def _set_SPSR_svc_Type_IL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_IL r v)

def _set_SPSR_und_Type_IL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_IL r v)

def _set_ESRType_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESRType_ISS r v)

def _set_DISR_EL1_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_EL1_Type_ISS r v)

def _set_ESR_EL1_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL1_Type_ISS r v)

def _set_ESR_EL2_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL2_Type_ISS r v)

def _set_ESR_EL3_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL3_Type_ISS r v)

def _set_HSR_Type_ISS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSR_Type_ISS r v)

def _set_VDISR_EL2_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_EL2_Type_ISS r v)

def _set_VSESR_EL2_Type_ISS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSESR_EL2_Type_ISS r v)

def _set_FPCRType_AH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_AH r v)

def _set_FPCR_Type_AH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_AH r v)

def _set_FPCRType_AHP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_AHP r v)

def _set_FPCR_Type_AHP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_AHP r v)

def _set_FPSCR_Type_AHP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_AHP r v)

def _set_FPCRType_DN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_DN r v)

def _set_FPCR_Type_DN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_DN r v)

def _set_FPSCR_Type_DN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_DN r v)

def _set_FPCRType_DZC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_DZC r v)

def _set_FPSCR_Type_DZC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_DZC r v)

def _set_FPSR_Type_DZC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_DZC r v)

def _set_FPCRType_EBF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_EBF r v)

def _set_FPCR_Type_EBF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_EBF r v)

def _set_FPCRType_FIZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_FIZ r v)

def _set_FPCR_Type_FIZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_FIZ r v)

def _set_FPCRType_FZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_FZ r v)

def _set_FPCR_Type_FZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_FZ r v)

def _set_FPSCR_Type_FZ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_FZ r v)

def _set_FPCRType_FZ16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_FZ16 r v)

def _set_FPCR_Type_FZ16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_FZ16 r v)

def _set_FPSCR_Type_FZ16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_FZ16 r v)

def _set_FPCRType_IDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_IDE r v)

def _set_FPCR_Type_IDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_IDE r v)

def _set_FPSCR_Type_IDE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_IDE r v)

def _set_FPCRType_IOC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_IOC r v)

def _set_FPSCR_Type_IOC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_IOC r v)

def _set_FPSR_Type_IOC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_IOC r v)

def _set_FPCRType_IOE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_IOE r v)

def _set_FPCR_Type_IOE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_IOE r v)

def _set_FPSCR_Type_IOE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_IOE r v)

def _set_FPCRType_IXE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_IXE r v)

def _set_FPCR_Type_IXE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_IXE r v)

def _set_FPSCR_Type_IXE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_IXE r v)

def _set_FPCRType_NEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_NEP r v)

def _set_FPCR_Type_NEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_NEP r v)

def _set_FPCRType_OFC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_OFC r v)

def _set_FPSCR_Type_OFC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_OFC r v)

def _set_FPSR_Type_OFC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_OFC r v)

def _set_FPCRType_OFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_OFE r v)

def _set_FPCR_Type_OFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_OFE r v)

def _set_FPSCR_Type_OFE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_OFE r v)

def _set_FPCRType_RMode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_RMode r v)

def _set_FPCR_Type_RMode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_RMode r v)

def _set_FPSCR_Type_RMode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_RMode r v)

def _set_FPCRType_Stride (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_Stride r v)

def _set_FPCR_Type_Stride (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_Stride r v)

def _set_FPSCR_Type_Stride (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_Stride r v)

def _set_FPCRType_UFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_UFE r v)

def _set_FPCR_Type_UFE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_UFE r v)

def _set_FPSCR_Type_UFE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_UFE r v)

def _set_FPCRType_length (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCRType_length r v)

def _set_FPCR_Type_length (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPCR_Type_length r v)

def _set_FPSCR_Type_length (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_length r v)

def _set_BRBSRCType_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBSRCType_ADDRESS r v)

def _set_BRBSRCINJ_EL1_Type_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBSRCINJ_EL1_Type_ADDRESS r v)

def _set_BRBSRC_EL1_Type_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBSRC_EL1_Type_ADDRESS r v)

def _set_BRBTGTINJ_EL1_Type_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBTGTINJ_EL1_Type_ADDRESS r v)

def _set_BRBTGTType_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBTGTType_ADDRESS r v)

def _set_BRBTGT_EL1_Type_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBTGT_EL1_Type_ADDRESS r v)

def _set_PMIAR_EL1_Type_ADDRESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMIAR_EL1_Type_ADDRESS r v)

def _set_BRBINFType_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 14)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFType_CC r v)

def _set_BRBCR_EL1_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL1_Type_CC r v)

def _set_BRBCR_EL2_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL2_Type_CC r v)

def _set_BRBIDR0_EL1_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBIDR0_EL1_Type_CC r v)

def _set_BRBINFINJ_EL1_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 14)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_CC r v)

def _set_BRBINF_EL1_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 14)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINF_EL1_Type_CC r v)

def _set_PMCFGR_Type_CC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_CC r v)

def _set_BRBINFType_CCU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFType_CCU r v)

def _set_BRBINFINJ_EL1_Type_CCU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_CCU r v)

def _set_BRBINF_EL1_Type_CCU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINF_EL1_Type_CCU r v)

def _set_BRBINFType_EL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFType_EL r v)

def _set_BRBINFINJ_EL1_Type_EL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_EL r v)

def _set_BRBINF_EL1_Type_EL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINF_EL1_Type_EL r v)

def _set_EDPCSR_Type_EL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPCSR_Type_EL r v)

def _set_PMPCSR_Type_EL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPCSR_Type_EL r v)

def _set_BRBINFType_LASTFAILED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFType_LASTFAILED r v)

def _set_BRBFCR_EL1_Type_LASTFAILED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_LASTFAILED r v)

def _set_BRBINFINJ_EL1_Type_LASTFAILED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_LASTFAILED r v)

def _set_BRBINF_EL1_Type_LASTFAILED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINF_EL1_Type_LASTFAILED r v)

def _set_BRBINFType_MPRED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFType_MPRED r v)

def _set_BRBCR_EL1_Type_MPRED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL1_Type_MPRED r v)

def _set_BRBCR_EL2_Type_MPRED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL2_Type_MPRED r v)

def _set_BRBINFINJ_EL1_Type_MPRED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_MPRED r v)

def _set_BRBINF_EL1_Type_MPRED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINF_EL1_Type_MPRED r v)

def _set_BRBINFType_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFType_T r v)

def _set_BRBINFINJ_EL1_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_T r v)

def _set_BRBINF_EL1_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINF_EL1_Type_T r v)

def _set_DSPSR_EL0_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_T r v)

def _set_DSPSR_Type_T (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_T r v)

def _set_PMCCFILTR_EL0_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_T r v)

def _set_PMEVTYPER_EL0_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_T r v)

def _set_PMICFILTR_EL0_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_T r v)

def _set_PMPCSR_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPCSR_Type_T r v)

def _set_SPSR_EL1_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_T r v)

def _set_SPSR_EL2_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_T r v)

def _set_SPSR_EL3_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_T r v)

def _set_SPSR_abt_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_T r v)

def _set_SPSR_fiq_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_T r v)

def _set_SPSR_hyp_Type_T (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_T r v)

def _set_SPSR_irq_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_T r v)

def _set_SPSR_mon_Type_T (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_T r v)

def _set_SPSR_svc_Type_T (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_T r v)

def _set_SPSR_und_Type_T (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_T r v)

def _set_BRBINFType_TYPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFType_TYPE r v)

def _set_BRBINFINJ_EL1_Type_TYPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_TYPE r v)

def _set_BRBINF_EL1_Type_TYPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINF_EL1_Type_TYPE r v)

def _set_BRBINFType_VALID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFType_VALID r v)

def _set_BRBINFINJ_EL1_Type_VALID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINFINJ_EL1_Type_VALID r v)

def _set_BRBINF_EL1_Type_VALID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBINF_EL1_Type_VALID r v)

def undefined_CacheRecord (_ : Unit) : SailM CacheRecord := do
  (pure { acctype := ← (do (undefined_AccessType ()))
          cacheop := ← (do (undefined_CacheOp ()))
          opscope := ← (do (undefined_CacheOpScope ()))
          cachetype := ← (do (undefined_CacheType ()))
          regval := ← (do (undefined_bitvector 64))
          paddress := ← (do (undefined_FullAddress ()))
          vaddress := ← (do (undefined_bitvector 64))
          setnum := ← (do (undefined_int ()))
          waynum := ← (do (undefined_int ()))
          level := ← (do (undefined_int ()))
          shareability := ← (do (undefined_Shareability ()))
          translated := ← (do (undefined_bool ()))
          is_vmid_valid := ← (do (undefined_bool ()))
          vmid := ← (do (undefined_bitvector 16))
          is_asid_valid := ← (do (undefined_bool ()))
          asid := ← (do (undefined_bitvector 16))
          security := ← (do (undefined_SecurityState ()))
          cpas := ← (do (undefined_CachePASpace ())) })

def undefined_ExecutionCntxt (_ : Unit) : SailM ExecutionCntxt := do
  (pure { is_vmid_valid := ← (do (undefined_bool ()))
          all_vmid := ← (do (undefined_bool ()))
          vmid := ← (do (undefined_bitvector 16))
          is_asid_valid := ← (do (undefined_bool ()))
          all_asid := ← (do (undefined_bool ()))
          asid := ← (do (undefined_bitvector 16))
          target_el := ← (do (undefined_bitvector 2))
          security := ← (do (undefined_SecurityState ()))
          restriction := ← (do (undefined_RestrictType ())) })

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def ignore_data_dependency (n : Nat) : Unit :=
  if ((n ≤b 30) : Bool)
  then (sail_ignore_write_to (register_ref n))
  else ()

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 -/
def ignore_dependency_edge (n : Nat) (m : Nat) : Unit :=
  if (((n ≤b 30) && (m ≤b 30)) : Bool)
  then (sail_mark_register_pair (register_ref n) (register_ref m) "ignore_edge")
  else ()

def _set_FPSR_Type_IDC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_IDC r v)

def _set_CTR_EL0_Type_IDC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_EL0_Type_IDC r v)

def _set_CTR_Type_IDC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_Type_IDC r v)

def _set_FPSCR_Type_IDC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_IDC r v)

def _set_FPSR_Type_IXC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_IXC r v)

def _set_FPSCR_Type_IXC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_IXC r v)

def _set_FPSR_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_N r v)

def _set_AMCFGR_EL0_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCFGR_EL0_Type_N r v)

def _set_AMCFGR_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCFGR_Type_N r v)

def _set_DSPSR_EL0_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_N r v)

def _set_DSPSR_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_N r v)

def _set_FPSCR_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_N r v)

def _set_PMCFGR_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_N r v)

def _set_PMCR_EL0_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_N r v)

def _set_PMCR_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_N r v)

def _set_SPSR_EL1_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_N r v)

def _set_SPSR_EL2_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_N r v)

def _set_SPSR_EL3_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_N r v)

def _set_SPSR_abt_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_N r v)

def _set_SPSR_fiq_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_N r v)

def _set_SPSR_hyp_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_N r v)

def _set_SPSR_irq_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_N r v)

def _set_SPSR_mon_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_N r v)

def _set_SPSR_svc_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_N r v)

def _set_SPSR_und_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_N r v)

def _set_TTBCR_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_N r v)

def _set_FPSR_Type_QC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_QC r v)

def _set_FPSCR_Type_QC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_QC r v)

def _set_FPSR_Type_UFC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_UFC r v)

def _set_FPSCR_Type_UFC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_UFC r v)

def _set_FPSR_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_V r v)

def _set_DSPSR_EL0_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_V r v)

def _set_DSPSR_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_V r v)

def _set_FPSCR_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_V r v)

def _set_GICR_INVALLR_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INVALLR_Type_V r v)

def _set_GICR_INVLPIR_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INVLPIR_Type_V r v)

def _set_SCTLR_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_V r v)

def _set_SPSR_EL1_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_V r v)

def _set_SPSR_EL2_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_V r v)

def _set_SPSR_EL3_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_V r v)

def _set_SPSR_abt_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_V r v)

def _set_SPSR_fiq_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_V r v)

def _set_SPSR_hyp_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_V r v)

def _set_SPSR_irq_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_V r v)

def _set_SPSR_mon_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_V r v)

def _set_SPSR_svc_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_V r v)

def _set_SPSR_und_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_V r v)

def _set_FPSR_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSR_Type_Z r v)

def _set_DSPSR_EL0_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_Z r v)

def _set_DSPSR_Type_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_Z r v)

def _set_FPSCR_Type_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSCR_Type_Z r v)

def _set_GICR_VPROPBASER_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Z r v)

def _set_SPSR_EL1_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_Z r v)

def _set_SPSR_EL2_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_Z r v)

def _set_SPSR_EL3_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_Z r v)

def _set_SPSR_abt_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_Z r v)

def _set_SPSR_fiq_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_Z r v)

def _set_SPSR_hyp_Type_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_Z r v)

def _set_SPSR_irq_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_Z r v)

def _set_SPSR_mon_Type_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_Z r v)

def _set_SPSR_svc_Type_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_Z r v)

def _set_SPSR_und_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_Z r v)

def _set_ICC_PMR_EL1_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_PMR_EL1_Type_Priority r v)

def _set_GICC_PMR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_PMR_Type_Priority r v)

def _set_GICC_RPR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_RPR_Type_Priority r v)

def _set_GICV_PMR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_PMR_Type_Priority r v)

def _set_GICV_RPR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_RPR_Type_Priority r v)

def _set_ICC_PMR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_PMR_Type_Priority r v)

def _set_ICC_RPR_EL1_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_RPR_EL1_Type_Priority r v)

def _set_ICC_RPR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_RPR_Type_Priority r v)

def _set_ICH_LRC_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LRC_Type_Priority r v)

def _set_ICH_LR_EL2_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_Priority r v)

def _set_ICV_PMR_EL1_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_PMR_EL1_Type_Priority r v)

def _set_ICV_PMR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_PMR_Type_Priority r v)

def _set_ICV_RPR_EL1_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_RPR_EL1_Type_Priority r v)

def _set_ICV_RPR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_RPR_Type_Priority r v)

def _set_SMPRI_EL1_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRI_EL1_Type_Priority r v)

def undefined_TLBIRecord (_ : Unit) : SailM TLBIRecord := do
  (pure { op := ← (do (undefined_TLBIOp ()))
          from_aarch64 := ← (do (undefined_bool ()))
          security := ← (do (undefined_SecurityState ()))
          regime := ← (do (undefined_Regime ()))
          vmid := ← (do (undefined_bitvector 16))
          asid := ← (do (undefined_bitvector 16))
          level := ← (do (undefined_TLBILevel ()))
          attr := ← (do (undefined_TLBIMemAttr ()))
          ipaspace := ← (do (undefined_PASpace ()))
          address := ← (do (undefined_bitvector 64))
          end_address_name := ← (do (undefined_bitvector 64))
          d64 := ← (do (undefined_bool ()))
          d128 := ← (do (undefined_bool ()))
          ttl := ← (do (undefined_bitvector 4))
          tg := ← (do (undefined_bitvector 2)) })

def _set_HCR_EL2_Type_AMO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_AMO r v)

def _set_HCR_Type_AMO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_AMO r v)

def _set_HCR_EL2_Type_AMVOFFEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_AMVOFFEN r v)

def _set_SCR_EL3_Type_AMVOFFEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_AMVOFFEN r v)

def _set_HCR_EL2_Type_API (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_API r v)

def _set_ID_AA64ISAR1_EL1_Type_API (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_API r v)

def _set_SCR_EL3_Type_API (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_API r v)

def _set_HCR_EL2_Type_APK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_APK r v)

def _set_SCR_EL3_Type_APK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_APK r v)

def _set_HCR_EL2_Type_AT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_AT r v)

def _set_ID_AA64MMFR2_EL1_Type_AT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_AT r v)

def _set_HCR_EL2_Type_ATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_ATA r v)

def _set_SCR_EL3_Type_ATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_ATA r v)

def _set_SCTLR_EL1_Type_ATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_ATA r v)

def _set_SCTLR_EL2_Type_ATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_ATA r v)

def _set_SCTLR_EL3_Type_ATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_ATA r v)

def _set_HCR_EL2_Type_BSU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_BSU r v)

def _set_HCR_Type_BSU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_BSU r v)

def _set_HCR_EL2_Type_CD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_CD r v)

def _set_HCR2_Type_CD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR2_Type_CD r v)

def _set_HCR_EL2_Type_DC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_DC r v)

def _set_HCR_Type_DC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_DC r v)

def _set_HCR_EL2_Type_DCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_DCT r v)

def _set_HCR_EL2_Type_E2H (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_E2H r v)

def _set_HCR_EL2_Type_EnSCXT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_EnSCXT r v)

def _set_SCR_EL3_Type_EnSCXT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_EnSCXT r v)

def _set_HCR_EL2_Type_FB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_FB r v)

def _set_HCR_Type_FB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_FB r v)

def _set_HCR_EL2_Type_FIEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_FIEN r v)

def _set_SCR_EL3_Type_FIEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_FIEN r v)

def _set_HCR_EL2_Type_FMO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_FMO r v)

def _set_HCR_Type_FMO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_FMO r v)

def _set_HCR_EL2_Type_FWB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_FWB r v)

def _set_ID_AA64MMFR2_EL1_Type_FWB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_FWB r v)

def _set_HCR_EL2_Type_GPF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_GPF r v)

def _set_SCR_EL3_Type_GPF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_GPF r v)

def _set_HCR_EL2_Type_HCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_HCD r v)

def _set_HCR_Type_HCD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_HCD r v)

def _set_HCR_EL2_Type_ID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_ID r v)

def _set_HCR2_Type_ID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR2_Type_ID r v)

def _set_HCR_EL2_Type_IMO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_IMO r v)

def _set_HCR_Type_IMO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_IMO r v)

def _set_HCR_EL2_Type_MIOCNCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_MIOCNCE r v)

def _set_HCR2_Type_MIOCNCE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR2_Type_MIOCNCE r v)

def _set_HCR_EL2_Type_NV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_NV r v)

def _set_ID_AA64MMFR2_EL1_Type_NV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_NV r v)

def _set_HCR_EL2_Type_NV1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_NV1 r v)

def _set_HCR_EL2_Type_NV2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_NV2 r v)

def _set_HCR_EL2_Type_PTW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_PTW r v)

def _set_HCR_Type_PTW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_PTW r v)

def _set_PAR_EL1_Type_PTW (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_PTW r v)

def _set_HCR_EL2_Type_SWIO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_SWIO r v)

def _set_HCR_Type_SWIO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_SWIO r v)

def _set_HCR_EL2_Type_TACR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TACR r v)

def _set_HCR_EL2_Type_TDZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TDZ r v)

def _set_HCR_EL2_Type_TEA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TEA r v)

def _set_HCR2_Type_TEA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR2_Type_TEA r v)

def _set_HCR_EL2_Type_TERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TERR r v)

def _set_HCR2_Type_TERR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR2_Type_TERR r v)

def _set_SCR_EL3_Type_TERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TERR r v)

def _set_SCR_Type_TERR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_Type_TERR r v)

def _set_HCR_EL2_Type_TGE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TGE r v)

def _set_HCR_Type_TGE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TGE r v)

def _set_HCR_EL2_Type_TICAB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TICAB r v)

def _set_HCR2_Type_TICAB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR2_Type_TICAB r v)

def _set_HCR_EL2_Type_TID0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TID0 r v)

def _set_HCR_Type_TID0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TID0 r v)

def _set_HCR_EL2_Type_TID1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TID1 r v)

def _set_HCR_Type_TID1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TID1 r v)

def _set_HCR_EL2_Type_TID2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TID2 r v)

def _set_HCR_Type_TID2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TID2 r v)

def _set_HCR_EL2_Type_TID3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TID3 r v)

def _set_HCR_Type_TID3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TID3 r v)

def _set_HCR_EL2_Type_TID4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TID4 r v)

def _set_HCR2_Type_TID4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR2_Type_TID4 r v)

def _set_HCR_EL2_Type_TID5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TID5 r v)

def _set_HCR_EL2_Type_TLOR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TLOR r v)

def _set_SCR_EL3_Type_TLOR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TLOR r v)

def _set_HCR_EL2_Type_TOCU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TOCU r v)

def _set_HCR2_Type_TOCU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR2_Type_TOCU r v)

def _set_HCR_EL2_Type_TPC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TPC r v)

def _set_HCR_Type_TPC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TPC r v)

def _set_HCR_EL2_Type_TPCP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TPCP r v)

def _set_HCR_EL2_Type_TPU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TPU r v)

def _set_HCR_Type_TPU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TPU r v)

def _set_HCR_EL2_Type_TRVM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TRVM r v)

def _set_HCR_Type_TRVM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TRVM r v)

def _set_HCR_EL2_Type_TSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TSC r v)

def _set_HCR_Type_TSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TSC r v)

def _set_HCR_EL2_Type_TSW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TSW r v)

def _set_HCR_Type_TSW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TSW r v)

def _set_HCR_EL2_Type_TTLB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TTLB r v)

def _set_HCR_Type_TTLB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TTLB r v)

def _set_HCR_EL2_Type_TTLBIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TTLBIS r v)

def _set_HCR2_Type_TTLBIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR2_Type_TTLBIS r v)

def _set_HCR_EL2_Type_TTLBOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TTLBOS r v)

def _set_HCR_EL2_Type_TVM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TVM r v)

def _set_HCR_Type_TVM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TVM r v)

def _set_HCR_EL2_Type_TWEDEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TWEDEL r v)

def _set_SCR_EL3_Type_TWEDEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TWEDEL r v)

def _set_SCTLR_EL1_Type_TWEDEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TWEDEL r v)

def _set_SCTLR_EL2_Type_TWEDEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TWEDEL r v)

def _set_HCR_EL2_Type_TWEDEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_TWEDEn r v)

def _set_SCR_EL3_Type_TWEDEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TWEDEn r v)

def _set_SCTLR_EL1_Type_TWEDEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TWEDEn r v)

def _set_SCTLR_EL2_Type_TWEDEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TWEDEn r v)

def _set_HCR_EL2_Type_VF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_VF r v)

def _set_HCR_Type_VF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_VF r v)

def _set_HCR_EL2_Type_VI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_VI r v)

def _set_HCR_Type_VI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_VI r v)

def _set_HCR_EL2_Type_VM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_VM r v)

def _set_HCR_Type_VM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_VM r v)

def _set_HCR_EL2_Type_VSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_EL2_Type_VSE r v)

def _set_SCR_EL3_Type_ADEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_ADEn r v)

def _set_SCR_EL3_Type_AIEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_AIEn r v)

def _set_SCR_EL3_Type_D128En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_D128En r v)

def _set_HCRX_EL2_Type_D128En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_D128En r v)

def _set_SCR_EL3_Type_EASE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_EASE r v)

def _set_SCTLR2_EL1_Type_EASE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL1_Type_EASE r v)

def _set_SCTLR2_EL2_Type_EASE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_EASE r v)

def _set_SCR_EL3_Type_ECVEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_ECVEn r v)

def _set_SCR_EL3_Type_EEL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_EEL2 r v)

def _set_SCR_EL3_Type_EnAS0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_EnAS0 r v)

def _set_HCRX_EL2_Type_EnAS0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_EnAS0 r v)

def _set_SCTLR_EL1_Type_EnAS0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnAS0 r v)

def _set_SCTLR_EL2_Type_EnAS0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnAS0 r v)

def _set_SCR_EL3_Type_EnIDCP128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_EnIDCP128 r v)

def _set_HCRX_EL2_Type_EnIDCP128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_EnIDCP128 r v)

def _set_SCTLR2_EL1_Type_EnIDCP128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL1_Type_EnIDCP128 r v)

def _set_SCTLR2_EL2_Type_EnIDCP128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_EnIDCP128 r v)

def _set_SCR_EL3_Type_EnTP2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_EnTP2 r v)

def _set_SCTLR_EL1_Type_EnTP2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnTP2 r v)

def _set_SCTLR_EL2_Type_EnTP2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnTP2 r v)

def _set_SCR_EL3_Type_FGTEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_FGTEn r v)

def _set_SCR_EL3_Type_FGTEn2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_FGTEn2 r v)

def _set_SCR_EL3_Type_GCSEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_GCSEn r v)

def _set_HCRX_EL2_Type_GCSEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_GCSEn r v)

def _set_SCR_EL3_Type_HXEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_HXEn r v)

def _set_SCR_EL3_Type_MECEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_MECEn r v)

def _set_SCR_EL3_Type_NMEA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_NMEA r v)

def _set_SCTLR2_EL1_Type_NMEA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL1_Type_NMEA r v)

def _set_SCTLR2_EL2_Type_NMEA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_NMEA r v)

def _set_SCR_EL3_Type_NSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_NSE r v)

def _set_EDSCR_Type_NSE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_NSE r v)

def _set_MFAR_EL3_Type_NSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MFAR_EL3_Type_NSE r v)

def _set_PAR_EL1_Type_NSE (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_NSE r v)

def _set_PFAR_EL1_Type_NSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PFAR_EL1_Type_NSE r v)

def _set_PFAR_EL2_Type_NSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PFAR_EL2_Type_NSE r v)

def _set_PMPCSR_Type_NSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPCSR_Type_NSE r v)

def _set_SCR_EL3_Type_PFAREn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_PFAREn r v)

def _set_SCR_EL3_Type_PIEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_PIEn r v)

def _set_SCR_EL3_Type_RCWMASKEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_RCWMASKEn r v)

def _set_SCR_EL3_Type_SCTLR2En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_SCTLR2En r v)

def _set_HCRX_EL2_Type_SCTLR2En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_SCTLR2En r v)

def _set_SCR_EL3_Type_TCR2En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TCR2En r v)

def _set_HCRX_EL2_Type_TCR2En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_TCR2En r v)

def _set_SCR_EL3_Type_TMEA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TMEA r v)

def _set_HCRX_EL2_Type_TMEA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_TMEA r v)

def _set_SCR_EL3_Type_TRNDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TRNDR r v)

def _set_SCR_EL3_Type_TWERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCR_EL3_Type_TWERR r v)

def FPCR_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (__get_FPCR (← readReg FPCR)) ) : SailM (BitVec 64) )
  (pure (Mk_FPCRType r))

def __get_FPSCR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : FPSCR_Type := value_name
  let tmp : FPSCR_Type := (Mk_FPSCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x6060#16 32))))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions"))) : Bool)
    then (pure (Mk_FPSCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x100#12 32)))))
    else (pure tmp) ) : SailM (BitVec 32) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions"))) : Bool)
    then (pure (Mk_FPSCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x200#12 32)))))
    else (pure tmp) ) : SailM (BitVec 32) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions"))) : Bool)
    then (pure (Mk_FPSCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x400#12 32)))))
    else (pure tmp) ) : SailM (BitVec 32) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions"))) : Bool)
    then (pure (Mk_FPSCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x800#12 32)))))
    else (pure tmp) ) : SailM (BitVec 32) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions"))) : Bool)
    then (pure (Mk_FPSCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1000#16 32)))))
    else (pure tmp) ) : SailM (BitVec 32) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions"))) : Bool)
    then (pure (Mk_FPSCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x8000#16 32)))))
    else (pure tmp) ) : SailM (BitVec 32) )
  if ((← (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ")) : Bool)
  then (pure (Mk_FPSCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x370000#24 32)))))
  else (pure tmp)

def _set_ERRnFR_ElemType_CE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_CE r v)

def _set_ERRnFR_ElemType_CEC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_CEC r v)

def _set_ERRnFR_ElemType_CEO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_CEO r v)

def _set_ERRnFR_ElemType_CFI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_CFI r v)

def _set_ERRnFR_ElemType_CI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_CI r v)

def _set_ERRnFR_ElemType_DE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_DE r v)

def _set_ERRnFR_ElemType_DUI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_DUI r v)

def _set_ERRnFR_ElemType_ED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_ED r v)

def _set_ERRnFR_ElemType_FI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_FI r v)

def _set_ERRnFR_ElemType_FRX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_FRX r v)

def _set_ERRnFR_ElemType_INJ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_INJ r v)

def _set_ERRnFR_ElemType_RP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_RP r v)

def _set_ERRnFR_ElemType_TS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_TS r v)

def _set_BRBCR_EL1_Type_TS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL1_Type_TS r v)

def _set_BRBCR_EL2_Type_TS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL2_Type_TS r v)

def _set_BRBTS_EL1_Type_TS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBTS_EL1_Type_TS r v)

def _set_HTRFCR_Type_TS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTRFCR_Type_TS r v)

def _set_ID_AA64ISAR0_EL1_Type_TS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_TS r v)

def _set_PMSCR_EL1_Type_TS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL1_Type_TS r v)

def _set_PMSCR_EL2_Type_TS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL2_Type_TS r v)

def _set_TRFCR_EL1_Type_TS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_EL1_Type_TS r v)

def _set_TRFCR_EL2_Type_TS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_EL2_Type_TS r v)

def _set_TRFCR_Type_TS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_Type_TS r v)

def _set_ERRnFR_ElemType_UC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_UC r v)

def _set_ERRnFR_ElemType_UE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_UE r v)

def _set_ERRnFR_ElemType_UEO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_UEO r v)

def _set_ERRnFR_ElemType_UER (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_UER r v)

def _set_ERRnFR_ElemType_UEU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_UEU r v)

def _set_ERRnFR_ElemType_UI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRnFR_ElemType_UI r v)

def _set_CTR_EL0_Type_CWG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_EL0_Type_CWG r v)

def _set_CTR_Type_CWG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_Type_CWG r v)

def _set_CTR_EL0_Type_DIC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_EL0_Type_DIC r v)

def _set_CTR_Type_DIC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_Type_DIC r v)

def _set_CTR_EL0_Type_DminLine (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_EL0_Type_DminLine r v)

def _set_CTR_Type_DminLine (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_Type_DminLine r v)

def _set_CTR_EL0_Type_ERG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_EL0_Type_ERG r v)

def _set_CTR_Type_ERG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_Type_ERG r v)

def _set_CTR_EL0_Type_IminLine (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_EL0_Type_IminLine r v)

def _set_CTR_Type_IminLine (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_Type_IminLine r v)

def _set_CTR_EL0_Type_L1Ip (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_EL0_Type_L1Ip r v)

def _set_CTR_Type_L1Ip (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_Type_L1Ip r v)

def _set_CTR_EL0_Type_TminLine (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTR_EL0_Type_TminLine r v)

def _set_HDCR_Type_HCCD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_HCCD r v)

def _set_MDCR_EL2_Type_HCCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_HCCD r v)

def _set_HDCR_Type_HLP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_HLP r v)

def _set_MDCR_EL2_Type_HLP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_HLP r v)

def _set_HDCR_Type_HPMD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_HPMD r v)

def _set_MDCR_EL2_Type_HPMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_HPMD r v)

def _set_HDCR_Type_HPME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_HPME r v)

def _set_MDCR_EL2_Type_HPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_HPME r v)

def _set_HDCR_Type_HPMFZO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_HPMFZO r v)

def _set_MDCR_EL2_Type_HPMFZO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_HPMFZO r v)

def _set_HDCR_Type_HPMN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_HPMN r v)

def _set_MDCR_EL2_Type_HPMN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_HPMN r v)

def _set_HDCR_Type_MTPME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_MTPME r v)

def _set_MDCR_EL2_Type_MTPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_MTPME r v)

def _set_MDCR_EL3_Type_MTPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_MTPME r v)

def _set_SDCR_Type_MTPME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDCR_Type_MTPME r v)

def _set_HDCR_Type_TDA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_TDA r v)

def _set_DBGDSCRext_Type_TDA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_TDA r v)

def _set_EDSCR_Type_TDA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_TDA r v)

def _set_MDCR_EL2_Type_TDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_TDA r v)

def _set_MDCR_EL3_Type_TDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_TDA r v)

def _set_MDSCR_EL1_Type_TDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_TDA r v)

def _set_HDCR_Type_TDCC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_TDCC r v)

def _set_MDCR_EL2_Type_TDCC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_TDCC r v)

def _set_MDCR_EL3_Type_TDCC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_TDCC r v)

def _set_MDSCR_EL1_Type_TDCC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_TDCC r v)

def _set_SDCR_Type_TDCC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDCR_Type_TDCC r v)

def _set_HDCR_Type_TDE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_TDE r v)

def _set_MDCR_EL2_Type_TDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_TDE r v)

def _set_HDCR_Type_TDOSA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_TDOSA r v)

def _set_MDCR_EL2_Type_TDOSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_TDOSA r v)

def _set_MDCR_EL3_Type_TDOSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_TDOSA r v)

def _set_HDCR_Type_TDRA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_TDRA r v)

def _set_MDCR_EL2_Type_TDRA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_TDRA r v)

def _set_HDCR_Type_TPM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_TPM r v)

def _set_MDCR_EL2_Type_TPM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_TPM r v)

def _set_MDCR_EL3_Type_TPM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_TPM r v)

def _set_HDCR_Type_TPMCR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_TPMCR r v)

def _set_MDCR_EL2_Type_TPMCR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_TPMCR r v)

def _set_HDCR_Type_TTRF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDCR_Type_TTRF r v)

def _set_MDCR_EL2_Type_TTRF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_TTRF r v)

def _set_MDCR_EL3_Type_TTRF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_TTRF r v)

def _set_SDCR_Type_TTRF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDCR_Type_TTRF r v)

def _set_MDCR_EL2_Type_E2PB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_E2PB r v)

def _set_MDCR_EL2_Type_EBWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_EBWE r v)

def _set_MDCR_EL3_Type_EBWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_EBWE r v)

def _set_MDCR_EL2_Type_EnSPM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_EnSPM r v)

def _set_MDSCR_EL1_Type_EnSPM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_EnSPM r v)

def _set_MDCR_EL2_Type_HPMFZS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_HPMFZS r v)

def _set_MDCR_EL2_Type_PMEE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_PMEE r v)

def _set_MDCR_EL3_Type_PMEE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_PMEE r v)

def _set_PMECR_EL1_Type_PMEE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMECR_EL1_Type_PMEE r v)

def _set_MDCR_EL2_Type_PMSSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_PMSSE r v)

def _set_MDCR_EL3_Type_PMSSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_PMSSE r v)

def _set_MDCR_EL2_Type_TPMS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL2_Type_TPMS r v)

def PMUCounterMask (_ : Unit) : SailM (BitVec 64) := do
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let n ← (( do
    if ((← (UsingAArch32 ())) : Bool)
    then (do (AArch32_GetNumEventCountersAccessible ()))
    else (do (AArch64_GetNumEventCountersAccessible ())) ) : SailM Int )
  let n := n
  sail_assert (n ≥b 0) "src/v8_base.sail:4047.30-4047.31"
  sail_assert (64 ≥b n) "src/v8_base.sail:4048.31-4048.32"
  let mask : (BitVec 64) := (Sail.BitVec.zeroExtend (Ones (n := n)) 64)
  let mask : (BitVec 64) := (BitVec.update mask CYCLE_COUNTER_ID (Bit 1#1))
  if ((←((HaveAArch64 ()) <&&> (do
       (HavePMUv3ICNTR ())))) : Bool)
  then (pure (BitVec.update mask INSTRUCTION_COUNTER_ID (Bit 1#1)))
  else (pure mask)

def _set_DBGDSCRext_Type_ERR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_ERR r v)

def _set_MDSCR_EL1_Type_ERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_ERR r v)

def _set_EDSCR_Type_HDE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_HDE r v)

def _set_DBGDSCRext_Type_HDE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_HDE r v)

def _set_MDSCR_EL1_Type_HDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_HDE r v)

def _set_EDSCR_Type_INTdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_INTdis r v)

def _set_DBGDSCRext_Type_INTdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_INTdis r v)

def _set_MDSCR_EL1_Type_INTdis (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_INTdis r v)

def _set_EDDFR1_Type_ITE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_ITE r v)

def _set_ID_AA64DFR1_EL1_Type_ITE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_ITE r v)

def _set_EDSCR_Type_PipeAdv (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_PipeAdv r v)

def _set_EDSCR_Type_RXO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_RXO r v)

def _set_DBGDSCRext_Type_RXO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_RXO r v)

def _set_MDSCR_EL1_Type_RXO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_RXO r v)

def _set_EDSCR_Type_RXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_RXfull r v)

def _set_DBGDSCRext_Type_RXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_RXfull r v)

def _set_DBGDSCRint_Type_RXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRint_Type_RXfull r v)

def _set_MDCCSR_EL0_Type_RXfull (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCCSR_EL0_Type_RXfull r v)

def _set_MDSCR_EL1_Type_RXfull (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_RXfull r v)

def _set_EDSCR_Type_SC2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_SC2 r v)

def _set_DBGDSCRext_Type_SC2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_SC2 r v)

def _set_MDSCR_EL1_Type_SC2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_SC2 r v)

def _set_MDCR_EL3_Type_SDD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_SDD r v)

def _set_DFSR_Type_STATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DFSR_Type_STATUS r v)

def _set_DISR_Type_STATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_Type_STATUS r v)

def _set_IFSR32_EL2_Type_STATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR32_EL2_Type_STATUS r v)

def _set_IFSR_Type_STATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR_Type_STATUS r v)

def _set_VDISR_EL2_Type_STATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_EL2_Type_STATUS r v)

def _set_VDISR_Type_STATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_Type_STATUS r v)

def _set_EDSCR_Type_TFO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_TFO r v)

def _set_DBGDSCRext_Type_TFO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_TFO r v)

def _set_MDSCR_EL1_Type_TFO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_TFO r v)

def _set_EDSCR_Type_TXU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_TXU r v)

def _set_DBGDSCRext_Type_TXU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_TXU r v)

def _set_MDSCR_EL1_Type_TXU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_TXU r v)

def _set_EDSCR_Type_TXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_TXfull r v)

def _set_DBGDSCRext_Type_TXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_TXfull r v)

def _set_DBGDSCRint_Type_TXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRint_Type_TXfull r v)

def _set_MDCCSR_EL0_Type_TXfull (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCCSR_EL0_Type_TXfull r v)

def _set_MDSCR_EL1_Type_TXfull (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_TXfull r v)

def _set_PMCNTENCLR_EL0_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_F0 r v)

def _set_PMCNTENSET_EL0_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_F0 r v)

def _set_PMCNTEN_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_F0 r v)

def _set_PMINTENCLR_EL1_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_F0 r v)

def _set_PMINTENSET_EL1_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_F0 r v)

def _set_PMINTEN_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_F0 r v)

def _set_PMOVSCLR_EL0_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_F0 r v)

def _set_PMOVSSET_EL0_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_F0 r v)

def _set_PMOVS_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_F0 r v)

def _set_PMUACR_EL1_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_F0 r v)

def _set_PMZR_EL0_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_F0 r v)

def _set_PMCNTENCLR_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P0 r v)

def _set_AMCNTENCLR0_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR0_EL0_Type_P0 r v)

def _set_AMCNTENCLR0_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR0_Type_P0 r v)

def _set_AMCNTENCLR1_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P0 r v)

def _set_AMCNTENCLR1_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P0 r v)

def _set_AMCNTENSET0_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET0_EL0_Type_P0 r v)

def _set_AMCNTENSET0_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET0_Type_P0 r v)

def _set_AMCNTENSET1_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P0 r v)

def _set_AMCNTENSET1_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P0 r v)

def _set_ICH_AP0R_EL2_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P0 r v)

def _set_ICH_AP0R_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P0 r v)

def _set_ICH_AP1R_EL2_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P0 r v)

def _set_ICH_AP1R_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P0 r v)

def _set_PMCNTENCLR_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P0 r v)

def _set_PMCNTENSET_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P0 r v)

def _set_PMCNTENSET_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P0 r v)

def _set_PMCNTEN_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P0 r v)

def _set_PMINTENCLR_EL1_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P0 r v)

def _set_PMINTENCLR_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P0 r v)

def _set_PMINTENSET_EL1_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P0 r v)

def _set_PMINTENSET_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P0 r v)

def _set_PMINTEN_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P0 r v)

def _set_PMOVSCLR_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P0 r v)

def _set_PMOVSR_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P0 r v)

def _set_PMOVSSET_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P0 r v)

def _set_PMOVSSET_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P0 r v)

def _set_PMOVS_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P0 r v)

def _set_PMSWINC_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P0 r v)

def _set_PMSWINC_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P0 r v)

def _set_PMUACR_EL1_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P0 r v)

def _set_PMZR_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P0 r v)

def _set_SMPRIMAP_EL2_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P0 r v)

def _set_SPMACCESSR_EL1_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P0 r v)

def _set_SPMACCESSR_EL2_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P0 r v)

def _set_SPMACCESSR_EL3_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P0 r v)

def _set_PMCNTENCLR_EL0_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P1 r v)

def _set_AMCNTENCLR0_EL0_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR0_EL0_Type_P1 r v)

def _set_AMCNTENCLR0_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR0_Type_P1 r v)

def _set_AMCNTENCLR1_EL0_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P1 r v)

def _set_AMCNTENCLR1_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P1 r v)

def _set_AMCNTENSET0_EL0_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET0_EL0_Type_P1 r v)

def _set_AMCNTENSET0_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET0_Type_P1 r v)

def _set_AMCNTENSET1_EL0_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P1 r v)

def _set_AMCNTENSET1_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P1 r v)

def _set_ICH_AP0R_EL2_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P1 r v)

def _set_ICH_AP0R_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P1 r v)

def _set_ICH_AP1R_EL2_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P1 r v)

def _set_ICH_AP1R_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P1 r v)

def _set_PMCNTENCLR_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P1 r v)

def _set_PMCNTENSET_EL0_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P1 r v)

def _set_PMCNTENSET_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P1 r v)

def _set_PMCNTEN_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P1 r v)

def _set_PMINTENCLR_EL1_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P1 r v)

def _set_PMINTENCLR_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P1 r v)

def _set_PMINTENSET_EL1_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P1 r v)

def _set_PMINTENSET_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P1 r v)

def _set_PMINTEN_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P1 r v)

def _set_PMOVSCLR_EL0_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P1 r v)

def _set_PMOVSR_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P1 r v)

def _set_PMOVSSET_EL0_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P1 r v)

def _set_PMOVSSET_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P1 r v)

def _set_PMOVS_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P1 r v)

def _set_PMSWINC_EL0_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P1 r v)

def _set_PMSWINC_Type_P1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P1 r v)

def _set_PMUACR_EL1_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P1 r v)

def _set_PMZR_EL0_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P1 r v)

def _set_SMPRIMAP_EL2_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P1 r v)

def _set_SPMACCESSR_EL1_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P1 r v)

def _set_SPMACCESSR_EL2_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P1 r v)

def _set_SPMACCESSR_EL3_Type_P1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P1 r v)

def _set_PMCNTENCLR_EL0_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P10 r v)

def _set_AMCNTENCLR1_EL0_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P10 r v)

def _set_AMCNTENCLR1_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P10 r v)

def _set_AMCNTENSET1_EL0_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P10 r v)

def _set_AMCNTENSET1_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P10 r v)

def _set_ICH_AP0R_EL2_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P10 r v)

def _set_ICH_AP0R_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P10 r v)

def _set_ICH_AP1R_EL2_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P10 r v)

def _set_ICH_AP1R_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P10 r v)

def _set_PMCNTENCLR_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P10 r v)

def _set_PMCNTENSET_EL0_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P10 r v)

def _set_PMCNTENSET_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P10 r v)

def _set_PMCNTEN_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P10 r v)

def _set_PMINTENCLR_EL1_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P10 r v)

def _set_PMINTENCLR_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P10 r v)

def _set_PMINTENSET_EL1_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P10 r v)

def _set_PMINTENSET_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P10 r v)

def _set_PMINTEN_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P10 r v)

def _set_PMOVSCLR_EL0_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P10 r v)

def _set_PMOVSR_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P10 r v)

def _set_PMOVSSET_EL0_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P10 r v)

def _set_PMOVSSET_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P10 r v)

def _set_PMOVS_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P10 r v)

def _set_PMSWINC_EL0_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P10 r v)

def _set_PMSWINC_Type_P10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P10 r v)

def _set_PMUACR_EL1_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P10 r v)

def _set_PMZR_EL0_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P10 r v)

def _set_SMPRIMAP_EL2_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P10 r v)

def _set_SPMACCESSR_EL1_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P10 r v)

def _set_SPMACCESSR_EL2_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P10 r v)

def _set_SPMACCESSR_EL3_Type_P10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P10 r v)

def _set_PMCNTENCLR_EL0_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P11 r v)

def _set_AMCNTENCLR1_EL0_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P11 r v)

def _set_AMCNTENCLR1_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P11 r v)

def _set_AMCNTENSET1_EL0_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P11 r v)

def _set_AMCNTENSET1_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P11 r v)

def _set_ICH_AP0R_EL2_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P11 r v)

def _set_ICH_AP0R_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P11 r v)

def _set_ICH_AP1R_EL2_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P11 r v)

def _set_ICH_AP1R_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P11 r v)

def _set_PMCNTENCLR_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P11 r v)

def _set_PMCNTENSET_EL0_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P11 r v)

def _set_PMCNTENSET_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P11 r v)

def _set_PMCNTEN_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P11 r v)

def _set_PMINTENCLR_EL1_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P11 r v)

def _set_PMINTENCLR_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P11 r v)

def _set_PMINTENSET_EL1_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P11 r v)

def _set_PMINTENSET_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P11 r v)

def _set_PMINTEN_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P11 r v)

def _set_PMOVSCLR_EL0_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P11 r v)

def _set_PMOVSR_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P11 r v)

def _set_PMOVSSET_EL0_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P11 r v)

def _set_PMOVSSET_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P11 r v)

def _set_PMOVS_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P11 r v)

def _set_PMSWINC_EL0_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P11 r v)

def _set_PMSWINC_Type_P11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P11 r v)

def _set_PMUACR_EL1_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P11 r v)

def _set_PMZR_EL0_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P11 r v)

def _set_SMPRIMAP_EL2_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P11 r v)

def _set_SPMACCESSR_EL1_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P11 r v)

def _set_SPMACCESSR_EL2_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P11 r v)

def _set_SPMACCESSR_EL3_Type_P11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P11 r v)

def _set_PMCNTENCLR_EL0_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P12 r v)

def _set_AMCNTENCLR1_EL0_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P12 r v)

def _set_AMCNTENCLR1_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P12 r v)

def _set_AMCNTENSET1_EL0_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P12 r v)

def _set_AMCNTENSET1_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P12 r v)

def _set_ICH_AP0R_EL2_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P12 r v)

def _set_ICH_AP0R_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P12 r v)

def _set_ICH_AP1R_EL2_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P12 r v)

def _set_ICH_AP1R_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P12 r v)

def _set_PMCNTENCLR_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P12 r v)

def _set_PMCNTENSET_EL0_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P12 r v)

def _set_PMCNTENSET_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P12 r v)

def _set_PMCNTEN_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P12 r v)

def _set_PMINTENCLR_EL1_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P12 r v)

def _set_PMINTENCLR_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P12 r v)

def _set_PMINTENSET_EL1_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P12 r v)

def _set_PMINTENSET_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P12 r v)

def _set_PMINTEN_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P12 r v)

def _set_PMOVSCLR_EL0_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P12 r v)

def _set_PMOVSR_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P12 r v)

def _set_PMOVSSET_EL0_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P12 r v)

def _set_PMOVSSET_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P12 r v)

def _set_PMOVS_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P12 r v)

def _set_PMSWINC_EL0_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P12 r v)

def _set_PMSWINC_Type_P12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P12 r v)

def _set_PMUACR_EL1_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P12 r v)

def _set_PMZR_EL0_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P12 r v)

def _set_SMPRIMAP_EL2_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P12 r v)

def _set_SPMACCESSR_EL1_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P12 r v)

def _set_SPMACCESSR_EL2_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P12 r v)

def _set_SPMACCESSR_EL3_Type_P12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P12 r v)

def _set_PMCNTENCLR_EL0_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P13 r v)

def _set_AMCNTENCLR1_EL0_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P13 r v)

def _set_AMCNTENCLR1_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P13 r v)

def _set_AMCNTENSET1_EL0_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P13 r v)

def _set_AMCNTENSET1_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P13 r v)

def _set_ICH_AP0R_EL2_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P13 r v)

def _set_ICH_AP0R_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P13 r v)

def _set_ICH_AP1R_EL2_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P13 r v)

def _set_ICH_AP1R_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P13 r v)

def _set_PMCNTENCLR_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P13 r v)

def _set_PMCNTENSET_EL0_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P13 r v)

def _set_PMCNTENSET_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P13 r v)

def _set_PMCNTEN_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P13 r v)

def _set_PMINTENCLR_EL1_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P13 r v)

def _set_PMINTENCLR_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P13 r v)

def _set_PMINTENSET_EL1_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P13 r v)

def _set_PMINTENSET_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P13 r v)

def _set_PMINTEN_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P13 r v)

def _set_PMOVSCLR_EL0_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P13 r v)

def _set_PMOVSR_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P13 r v)

def _set_PMOVSSET_EL0_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P13 r v)

def _set_PMOVSSET_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P13 r v)

def _set_PMOVS_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P13 r v)

def _set_PMSWINC_EL0_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P13 r v)

def _set_PMSWINC_Type_P13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P13 r v)

def _set_PMUACR_EL1_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P13 r v)

def _set_PMZR_EL0_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P13 r v)

def _set_SMPRIMAP_EL2_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P13 r v)

def _set_SPMACCESSR_EL1_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P13 r v)

def _set_SPMACCESSR_EL2_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P13 r v)

def _set_SPMACCESSR_EL3_Type_P13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P13 r v)

def _set_PMCNTENCLR_EL0_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P14 r v)

def _set_AMCNTENCLR1_EL0_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P14 r v)

def _set_AMCNTENCLR1_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P14 r v)

def _set_AMCNTENSET1_EL0_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P14 r v)

def _set_AMCNTENSET1_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P14 r v)

def _set_ICH_AP0R_EL2_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P14 r v)

def _set_ICH_AP0R_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P14 r v)

def _set_ICH_AP1R_EL2_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P14 r v)

def _set_ICH_AP1R_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P14 r v)

def _set_PMCNTENCLR_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P14 r v)

def _set_PMCNTENSET_EL0_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P14 r v)

def _set_PMCNTENSET_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P14 r v)

def _set_PMCNTEN_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P14 r v)

def _set_PMINTENCLR_EL1_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P14 r v)

def _set_PMINTENCLR_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P14 r v)

def _set_PMINTENSET_EL1_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P14 r v)

def _set_PMINTENSET_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P14 r v)

def _set_PMINTEN_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P14 r v)

def _set_PMOVSCLR_EL0_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P14 r v)

def _set_PMOVSR_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P14 r v)

def _set_PMOVSSET_EL0_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P14 r v)

def _set_PMOVSSET_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P14 r v)

def _set_PMOVS_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P14 r v)

def _set_PMSWINC_EL0_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P14 r v)

def _set_PMSWINC_Type_P14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P14 r v)

def _set_PMUACR_EL1_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P14 r v)

def _set_PMZR_EL0_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P14 r v)

def _set_SMPRIMAP_EL2_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P14 r v)

def _set_SPMACCESSR_EL1_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P14 r v)

def _set_SPMACCESSR_EL2_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P14 r v)

def _set_SPMACCESSR_EL3_Type_P14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P14 r v)

def _set_PMCNTENCLR_EL0_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P15 r v)

def _set_AMCNTENCLR1_EL0_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P15 r v)

def _set_AMCNTENCLR1_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P15 r v)

def _set_AMCNTENSET1_EL0_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P15 r v)

def _set_AMCNTENSET1_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P15 r v)

def _set_ICH_AP0R_EL2_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P15 r v)

def _set_ICH_AP0R_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P15 r v)

def _set_ICH_AP1R_EL2_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P15 r v)

def _set_ICH_AP1R_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P15 r v)

def _set_PMCNTENCLR_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P15 r v)

def _set_PMCNTENSET_EL0_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P15 r v)

def _set_PMCNTENSET_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P15 r v)

def _set_PMCNTEN_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P15 r v)

def _set_PMINTENCLR_EL1_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P15 r v)

def _set_PMINTENCLR_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P15 r v)

def _set_PMINTENSET_EL1_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P15 r v)

def _set_PMINTENSET_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P15 r v)

def _set_PMINTEN_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P15 r v)

def _set_PMOVSCLR_EL0_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P15 r v)

def _set_PMOVSR_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P15 r v)

def _set_PMOVSSET_EL0_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P15 r v)

def _set_PMOVSSET_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P15 r v)

def _set_PMOVS_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P15 r v)

def _set_PMSWINC_EL0_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P15 r v)

def _set_PMSWINC_Type_P15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P15 r v)

def _set_PMUACR_EL1_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P15 r v)

def _set_PMZR_EL0_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P15 r v)

def _set_SMPRIMAP_EL2_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P15 r v)

def _set_SPMACCESSR_EL1_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P15 r v)

def _set_SPMACCESSR_EL2_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P15 r v)

def _set_SPMACCESSR_EL3_Type_P15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P15 r v)

def _set_PMCNTENCLR_EL0_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P16 r v)

def _set_ICH_AP0R_EL2_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P16 r v)

def _set_ICH_AP0R_Type_P16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P16 r v)

def _set_ICH_AP1R_EL2_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P16 r v)

def _set_ICH_AP1R_Type_P16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P16 r v)

def _set_PMCNTENCLR_Type_P16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P16 r v)

def _set_PMCNTENSET_EL0_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P16 r v)

def _set_PMCNTENSET_Type_P16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P16 r v)

def _set_PMCNTEN_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P16 r v)

def _set_PMINTENCLR_EL1_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P16 r v)

def _set_PMINTENCLR_Type_P16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P16 r v)

def _set_PMINTENSET_EL1_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P16 r v)

def _set_PMINTENSET_Type_P16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P16 r v)

def _set_PMINTEN_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P16 r v)

def _set_PMOVSCLR_EL0_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P16 r v)

def _set_PMOVSR_Type_P16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P16 r v)

def _set_PMOVSSET_EL0_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P16 r v)

def _set_PMOVSSET_Type_P16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P16 r v)

def _set_PMOVS_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P16 r v)

def _set_PMSWINC_EL0_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P16 r v)

def _set_PMSWINC_Type_P16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P16 r v)

def _set_PMUACR_EL1_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P16 r v)

def _set_PMZR_EL0_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P16 r v)

def _set_SPMACCESSR_EL1_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P16 r v)

def _set_SPMACCESSR_EL2_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P16 r v)

def _set_SPMACCESSR_EL3_Type_P16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P16 r v)

def _set_PMCNTENCLR_EL0_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P17 r v)

def _set_ICH_AP0R_EL2_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P17 r v)

def _set_ICH_AP0R_Type_P17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P17 r v)

def _set_ICH_AP1R_EL2_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P17 r v)

def _set_ICH_AP1R_Type_P17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P17 r v)

def _set_PMCNTENCLR_Type_P17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P17 r v)

def _set_PMCNTENSET_EL0_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P17 r v)

def _set_PMCNTENSET_Type_P17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P17 r v)

def _set_PMCNTEN_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P17 r v)

def _set_PMINTENCLR_EL1_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P17 r v)

def _set_PMINTENCLR_Type_P17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P17 r v)

def _set_PMINTENSET_EL1_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P17 r v)

def _set_PMINTENSET_Type_P17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P17 r v)

def _set_PMINTEN_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P17 r v)

def _set_PMOVSCLR_EL0_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P17 r v)

def _set_PMOVSR_Type_P17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P17 r v)

def _set_PMOVSSET_EL0_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P17 r v)

def _set_PMOVSSET_Type_P17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P17 r v)

def _set_PMOVS_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P17 r v)

def _set_PMSWINC_EL0_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P17 r v)

def _set_PMSWINC_Type_P17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P17 r v)

def _set_PMUACR_EL1_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P17 r v)

def _set_PMZR_EL0_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P17 r v)

def _set_SPMACCESSR_EL1_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P17 r v)

def _set_SPMACCESSR_EL2_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P17 r v)

def _set_SPMACCESSR_EL3_Type_P17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P17 r v)

def _set_PMCNTENCLR_EL0_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P18 r v)

def _set_ICH_AP0R_EL2_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P18 r v)

def _set_ICH_AP0R_Type_P18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P18 r v)

def _set_ICH_AP1R_EL2_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P18 r v)

def _set_ICH_AP1R_Type_P18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P18 r v)

def _set_PMCNTENCLR_Type_P18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P18 r v)

def _set_PMCNTENSET_EL0_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P18 r v)

def _set_PMCNTENSET_Type_P18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P18 r v)

def _set_PMCNTEN_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P18 r v)

def _set_PMINTENCLR_EL1_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P18 r v)

def _set_PMINTENCLR_Type_P18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P18 r v)

def _set_PMINTENSET_EL1_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P18 r v)

def _set_PMINTENSET_Type_P18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P18 r v)

def _set_PMINTEN_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P18 r v)

def _set_PMOVSCLR_EL0_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P18 r v)

def _set_PMOVSR_Type_P18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P18 r v)

def _set_PMOVSSET_EL0_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P18 r v)

def _set_PMOVSSET_Type_P18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P18 r v)

def _set_PMOVS_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P18 r v)

def _set_PMSWINC_EL0_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P18 r v)

def _set_PMSWINC_Type_P18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P18 r v)

def _set_PMUACR_EL1_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P18 r v)

def _set_PMZR_EL0_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P18 r v)

def _set_SPMACCESSR_EL1_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P18 r v)

def _set_SPMACCESSR_EL2_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P18 r v)

def _set_SPMACCESSR_EL3_Type_P18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P18 r v)

def _set_PMCNTENCLR_EL0_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P19 r v)

def _set_ICH_AP0R_EL2_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P19 r v)

def _set_ICH_AP0R_Type_P19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P19 r v)

def _set_ICH_AP1R_EL2_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P19 r v)

def _set_ICH_AP1R_Type_P19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P19 r v)

def _set_PMCNTENCLR_Type_P19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P19 r v)

def _set_PMCNTENSET_EL0_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P19 r v)

def _set_PMCNTENSET_Type_P19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P19 r v)

def _set_PMCNTEN_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P19 r v)

def _set_PMINTENCLR_EL1_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P19 r v)

def _set_PMINTENCLR_Type_P19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P19 r v)

def _set_PMINTENSET_EL1_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P19 r v)

def _set_PMINTENSET_Type_P19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P19 r v)

def _set_PMINTEN_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P19 r v)

def _set_PMOVSCLR_EL0_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P19 r v)

def _set_PMOVSR_Type_P19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P19 r v)

def _set_PMOVSSET_EL0_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P19 r v)

def _set_PMOVSSET_Type_P19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P19 r v)

def _set_PMOVS_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P19 r v)

def _set_PMSWINC_EL0_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P19 r v)

def _set_PMSWINC_Type_P19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P19 r v)

def _set_PMUACR_EL1_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P19 r v)

def _set_PMZR_EL0_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P19 r v)

def _set_SPMACCESSR_EL1_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P19 r v)

def _set_SPMACCESSR_EL2_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P19 r v)

def _set_SPMACCESSR_EL3_Type_P19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P19 r v)

def _set_PMCNTENCLR_EL0_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P2 r v)

def _set_AMCNTENCLR0_EL0_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR0_EL0_Type_P2 r v)

def _set_AMCNTENCLR0_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR0_Type_P2 r v)

def _set_AMCNTENCLR1_EL0_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P2 r v)

def _set_AMCNTENCLR1_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P2 r v)

def _set_AMCNTENSET0_EL0_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET0_EL0_Type_P2 r v)

def _set_AMCNTENSET0_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET0_Type_P2 r v)

def _set_AMCNTENSET1_EL0_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P2 r v)

def _set_AMCNTENSET1_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P2 r v)

def _set_ICH_AP0R_EL2_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P2 r v)

def _set_ICH_AP0R_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P2 r v)

def _set_ICH_AP1R_EL2_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P2 r v)

def _set_ICH_AP1R_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P2 r v)

def _set_PMCNTENCLR_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P2 r v)

def _set_PMCNTENSET_EL0_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P2 r v)

def _set_PMCNTENSET_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P2 r v)

def _set_PMCNTEN_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P2 r v)

def _set_PMINTENCLR_EL1_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P2 r v)

def _set_PMINTENCLR_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P2 r v)

def _set_PMINTENSET_EL1_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P2 r v)

def _set_PMINTENSET_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P2 r v)

def _set_PMINTEN_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P2 r v)

def _set_PMOVSCLR_EL0_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P2 r v)

def _set_PMOVSR_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P2 r v)

def _set_PMOVSSET_EL0_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P2 r v)

def _set_PMOVSSET_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P2 r v)

def _set_PMOVS_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P2 r v)

def _set_PMSWINC_EL0_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P2 r v)

def _set_PMSWINC_Type_P2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P2 r v)

def _set_PMUACR_EL1_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P2 r v)

def _set_PMZR_EL0_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P2 r v)

def _set_SMPRIMAP_EL2_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P2 r v)

def _set_SPMACCESSR_EL1_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P2 r v)

def _set_SPMACCESSR_EL2_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P2 r v)

def _set_SPMACCESSR_EL3_Type_P2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P2 r v)

def _set_PMCNTENCLR_EL0_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P20 r v)

def _set_ICH_AP0R_EL2_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P20 r v)

def _set_ICH_AP0R_Type_P20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P20 r v)

def _set_ICH_AP1R_EL2_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P20 r v)

def _set_ICH_AP1R_Type_P20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P20 r v)

def _set_PMCNTENCLR_Type_P20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P20 r v)

def _set_PMCNTENSET_EL0_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P20 r v)

def _set_PMCNTENSET_Type_P20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P20 r v)

def _set_PMCNTEN_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P20 r v)

def _set_PMINTENCLR_EL1_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P20 r v)

def _set_PMINTENCLR_Type_P20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P20 r v)

def _set_PMINTENSET_EL1_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P20 r v)

def _set_PMINTENSET_Type_P20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P20 r v)

def _set_PMINTEN_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P20 r v)

def _set_PMOVSCLR_EL0_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P20 r v)

def _set_PMOVSR_Type_P20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P20 r v)

def _set_PMOVSSET_EL0_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P20 r v)

def _set_PMOVSSET_Type_P20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P20 r v)

def _set_PMOVS_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P20 r v)

def _set_PMSWINC_EL0_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P20 r v)

def _set_PMSWINC_Type_P20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P20 r v)

def _set_PMUACR_EL1_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P20 r v)

def _set_PMZR_EL0_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P20 r v)

def _set_SPMACCESSR_EL1_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P20 r v)

def _set_SPMACCESSR_EL2_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P20 r v)

def _set_SPMACCESSR_EL3_Type_P20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P20 r v)

def _set_PMCNTENCLR_EL0_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P21 r v)

def _set_ICH_AP0R_EL2_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P21 r v)

def _set_ICH_AP0R_Type_P21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P21 r v)

def _set_ICH_AP1R_EL2_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P21 r v)

def _set_ICH_AP1R_Type_P21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P21 r v)

def _set_PMCNTENCLR_Type_P21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P21 r v)

def _set_PMCNTENSET_EL0_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P21 r v)

def _set_PMCNTENSET_Type_P21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P21 r v)

def _set_PMCNTEN_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P21 r v)

def _set_PMINTENCLR_EL1_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P21 r v)

def _set_PMINTENCLR_Type_P21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P21 r v)

def _set_PMINTENSET_EL1_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P21 r v)

def _set_PMINTENSET_Type_P21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P21 r v)

def _set_PMINTEN_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P21 r v)

def _set_PMOVSCLR_EL0_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P21 r v)

def _set_PMOVSR_Type_P21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P21 r v)

def _set_PMOVSSET_EL0_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P21 r v)

def _set_PMOVSSET_Type_P21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P21 r v)

def _set_PMOVS_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P21 r v)

def _set_PMSWINC_EL0_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P21 r v)

def _set_PMSWINC_Type_P21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P21 r v)

def _set_PMUACR_EL1_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P21 r v)

def _set_PMZR_EL0_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P21 r v)

def _set_SPMACCESSR_EL1_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P21 r v)

def _set_SPMACCESSR_EL2_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P21 r v)

def _set_SPMACCESSR_EL3_Type_P21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P21 r v)

def _set_PMCNTENCLR_EL0_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P22 r v)

def _set_ICH_AP0R_EL2_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P22 r v)

def _set_ICH_AP0R_Type_P22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P22 r v)

def _set_ICH_AP1R_EL2_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P22 r v)

def _set_ICH_AP1R_Type_P22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P22 r v)

def _set_PMCNTENCLR_Type_P22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P22 r v)

def _set_PMCNTENSET_EL0_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P22 r v)

def _set_PMCNTENSET_Type_P22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P22 r v)

def _set_PMCNTEN_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P22 r v)

def _set_PMINTENCLR_EL1_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P22 r v)

def _set_PMINTENCLR_Type_P22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P22 r v)

def _set_PMINTENSET_EL1_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P22 r v)

def _set_PMINTENSET_Type_P22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P22 r v)

def _set_PMINTEN_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P22 r v)

def _set_PMOVSCLR_EL0_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P22 r v)

def _set_PMOVSR_Type_P22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P22 r v)

def _set_PMOVSSET_EL0_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P22 r v)

def _set_PMOVSSET_Type_P22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P22 r v)

def _set_PMOVS_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P22 r v)

def _set_PMSWINC_EL0_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P22 r v)

def _set_PMSWINC_Type_P22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P22 r v)

def _set_PMUACR_EL1_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P22 r v)

def _set_PMZR_EL0_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P22 r v)

def _set_SPMACCESSR_EL1_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P22 r v)

def _set_SPMACCESSR_EL2_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P22 r v)

def _set_SPMACCESSR_EL3_Type_P22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P22 r v)

def _set_PMCNTENCLR_EL0_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P23 r v)

def _set_ICH_AP0R_EL2_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P23 r v)

def _set_ICH_AP0R_Type_P23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P23 r v)

def _set_ICH_AP1R_EL2_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P23 r v)

def _set_ICH_AP1R_Type_P23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P23 r v)

def _set_PMCNTENCLR_Type_P23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P23 r v)

def _set_PMCNTENSET_EL0_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P23 r v)

def _set_PMCNTENSET_Type_P23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P23 r v)

def _set_PMCNTEN_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P23 r v)

def _set_PMINTENCLR_EL1_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P23 r v)

def _set_PMINTENCLR_Type_P23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P23 r v)

def _set_PMINTENSET_EL1_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P23 r v)

def _set_PMINTENSET_Type_P23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P23 r v)

def _set_PMINTEN_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P23 r v)

def _set_PMOVSCLR_EL0_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P23 r v)

def _set_PMOVSR_Type_P23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P23 r v)

def _set_PMOVSSET_EL0_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P23 r v)

def _set_PMOVSSET_Type_P23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P23 r v)

def _set_PMOVS_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P23 r v)

def _set_PMSWINC_EL0_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P23 r v)

def _set_PMSWINC_Type_P23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P23 r v)

def _set_PMUACR_EL1_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P23 r v)

def _set_PMZR_EL0_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P23 r v)

def _set_SPMACCESSR_EL1_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P23 r v)

def _set_SPMACCESSR_EL2_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P23 r v)

def _set_SPMACCESSR_EL3_Type_P23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P23 r v)

def _set_PMCNTENCLR_EL0_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P24 r v)

def _set_ICH_AP0R_EL2_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P24 r v)

def _set_ICH_AP0R_Type_P24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P24 r v)

def _set_ICH_AP1R_EL2_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P24 r v)

def _set_ICH_AP1R_Type_P24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P24 r v)

def _set_PMCNTENCLR_Type_P24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P24 r v)

def _set_PMCNTENSET_EL0_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P24 r v)

def _set_PMCNTENSET_Type_P24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P24 r v)

def _set_PMCNTEN_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P24 r v)

def _set_PMINTENCLR_EL1_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P24 r v)

def _set_PMINTENCLR_Type_P24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P24 r v)

def _set_PMINTENSET_EL1_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P24 r v)

def _set_PMINTENSET_Type_P24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P24 r v)

def _set_PMINTEN_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P24 r v)

def _set_PMOVSCLR_EL0_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P24 r v)

def _set_PMOVSR_Type_P24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P24 r v)

def _set_PMOVSSET_EL0_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P24 r v)

def _set_PMOVSSET_Type_P24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P24 r v)

def _set_PMOVS_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P24 r v)

def _set_PMSWINC_EL0_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P24 r v)

def _set_PMSWINC_Type_P24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P24 r v)

def _set_PMUACR_EL1_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P24 r v)

def _set_PMZR_EL0_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P24 r v)

def _set_SPMACCESSR_EL1_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P24 r v)

def _set_SPMACCESSR_EL2_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P24 r v)

def _set_SPMACCESSR_EL3_Type_P24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P24 r v)

def _set_PMCNTENCLR_EL0_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P25 r v)

def _set_ICH_AP0R_EL2_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P25 r v)

def _set_ICH_AP0R_Type_P25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P25 r v)

def _set_ICH_AP1R_EL2_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P25 r v)

def _set_ICH_AP1R_Type_P25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P25 r v)

def _set_PMCNTENCLR_Type_P25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P25 r v)

def _set_PMCNTENSET_EL0_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P25 r v)

def _set_PMCNTENSET_Type_P25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P25 r v)

def _set_PMCNTEN_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P25 r v)

def _set_PMINTENCLR_EL1_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P25 r v)

def _set_PMINTENCLR_Type_P25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P25 r v)

def _set_PMINTENSET_EL1_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P25 r v)

def _set_PMINTENSET_Type_P25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P25 r v)

def _set_PMINTEN_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P25 r v)

def _set_PMOVSCLR_EL0_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P25 r v)

def _set_PMOVSR_Type_P25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P25 r v)

def _set_PMOVSSET_EL0_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P25 r v)

def _set_PMOVSSET_Type_P25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P25 r v)

def _set_PMOVS_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P25 r v)

def _set_PMSWINC_EL0_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P25 r v)

def _set_PMSWINC_Type_P25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P25 r v)

def _set_PMUACR_EL1_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P25 r v)

def _set_PMZR_EL0_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P25 r v)

def _set_SPMACCESSR_EL1_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P25 r v)

def _set_SPMACCESSR_EL2_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P25 r v)

def _set_SPMACCESSR_EL3_Type_P25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P25 r v)

def _set_PMCNTENCLR_EL0_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P26 r v)

def _set_ICH_AP0R_EL2_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P26 r v)

def _set_ICH_AP0R_Type_P26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P26 r v)

def _set_ICH_AP1R_EL2_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P26 r v)

def _set_ICH_AP1R_Type_P26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P26 r v)

def _set_PMCNTENCLR_Type_P26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P26 r v)

def _set_PMCNTENSET_EL0_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P26 r v)

def _set_PMCNTENSET_Type_P26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P26 r v)

def _set_PMCNTEN_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P26 r v)

def _set_PMINTENCLR_EL1_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P26 r v)

def _set_PMINTENCLR_Type_P26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P26 r v)

def _set_PMINTENSET_EL1_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P26 r v)

def _set_PMINTENSET_Type_P26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P26 r v)

def _set_PMINTEN_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P26 r v)

def _set_PMOVSCLR_EL0_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P26 r v)

def _set_PMOVSR_Type_P26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P26 r v)

def _set_PMOVSSET_EL0_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P26 r v)

def _set_PMOVSSET_Type_P26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P26 r v)

def _set_PMOVS_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P26 r v)

def _set_PMSWINC_EL0_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P26 r v)

def _set_PMSWINC_Type_P26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P26 r v)

def _set_PMUACR_EL1_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P26 r v)

def _set_PMZR_EL0_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P26 r v)

def _set_SPMACCESSR_EL1_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P26 r v)

def _set_SPMACCESSR_EL2_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P26 r v)

def _set_SPMACCESSR_EL3_Type_P26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P26 r v)

def _set_PMCNTENCLR_EL0_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P27 r v)

def _set_ICH_AP0R_EL2_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P27 r v)

def _set_ICH_AP0R_Type_P27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P27 r v)

def _set_ICH_AP1R_EL2_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P27 r v)

def _set_ICH_AP1R_Type_P27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P27 r v)

def _set_PMCNTENCLR_Type_P27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P27 r v)

def _set_PMCNTENSET_EL0_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P27 r v)

def _set_PMCNTENSET_Type_P27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P27 r v)

def _set_PMCNTEN_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P27 r v)

def _set_PMINTENCLR_EL1_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P27 r v)

def _set_PMINTENCLR_Type_P27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P27 r v)

def _set_PMINTENSET_EL1_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P27 r v)

def _set_PMINTENSET_Type_P27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P27 r v)

def _set_PMINTEN_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P27 r v)

def _set_PMOVSCLR_EL0_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P27 r v)

def _set_PMOVSR_Type_P27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P27 r v)

def _set_PMOVSSET_EL0_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P27 r v)

def _set_PMOVSSET_Type_P27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P27 r v)

def _set_PMOVS_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P27 r v)

def _set_PMSWINC_EL0_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P27 r v)

def _set_PMSWINC_Type_P27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P27 r v)

def _set_PMUACR_EL1_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P27 r v)

def _set_PMZR_EL0_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P27 r v)

def _set_SPMACCESSR_EL1_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P27 r v)

def _set_SPMACCESSR_EL2_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P27 r v)

def _set_SPMACCESSR_EL3_Type_P27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P27 r v)

def _set_PMCNTENCLR_EL0_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P28 r v)

def _set_ICH_AP0R_EL2_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P28 r v)

def _set_ICH_AP0R_Type_P28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P28 r v)

def _set_ICH_AP1R_EL2_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P28 r v)

def _set_ICH_AP1R_Type_P28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P28 r v)

def _set_PMCNTENCLR_Type_P28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P28 r v)

def _set_PMCNTENSET_EL0_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P28 r v)

def _set_PMCNTENSET_Type_P28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P28 r v)

def _set_PMCNTEN_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P28 r v)

def _set_PMINTENCLR_EL1_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P28 r v)

def _set_PMINTENCLR_Type_P28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P28 r v)

def _set_PMINTENSET_EL1_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P28 r v)

def _set_PMINTENSET_Type_P28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P28 r v)

def _set_PMINTEN_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P28 r v)


