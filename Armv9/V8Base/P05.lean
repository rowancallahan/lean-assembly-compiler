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
import Armv9.V8Base.P02

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

def _set_PMOVSCLR_EL0_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P28 r v)

def _set_PMOVSR_Type_P28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P28 r v)

def _set_PMOVSSET_EL0_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P28 r v)

def _set_PMOVSSET_Type_P28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P28 r v)

def _set_PMOVS_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P28 r v)

def _set_PMSWINC_EL0_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P28 r v)

def _set_PMSWINC_Type_P28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P28 r v)

def _set_PMUACR_EL1_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P28 r v)

def _set_PMZR_EL0_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P28 r v)

def _set_SPMACCESSR_EL1_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P28 r v)

def _set_SPMACCESSR_EL2_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P28 r v)

def _set_SPMACCESSR_EL3_Type_P28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P28 r v)

def _set_PMCNTENCLR_EL0_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P29 r v)

def _set_ICH_AP0R_EL2_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P29 r v)

def _set_ICH_AP0R_Type_P29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P29 r v)

def _set_ICH_AP1R_EL2_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P29 r v)

def _set_ICH_AP1R_Type_P29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P29 r v)

def _set_PMCNTENCLR_Type_P29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P29 r v)

def _set_PMCNTENSET_EL0_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P29 r v)

def _set_PMCNTENSET_Type_P29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P29 r v)

def _set_PMCNTEN_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P29 r v)

def _set_PMINTENCLR_EL1_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P29 r v)

def _set_PMINTENCLR_Type_P29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P29 r v)

def _set_PMINTENSET_EL1_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P29 r v)

def _set_PMINTENSET_Type_P29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P29 r v)

def _set_PMINTEN_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P29 r v)

def _set_PMOVSCLR_EL0_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P29 r v)

def _set_PMOVSR_Type_P29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P29 r v)

def _set_PMOVSSET_EL0_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P29 r v)

def _set_PMOVSSET_Type_P29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P29 r v)

def _set_PMOVS_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P29 r v)

def _set_PMSWINC_EL0_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P29 r v)

def _set_PMSWINC_Type_P29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P29 r v)

def _set_PMUACR_EL1_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P29 r v)

def _set_PMZR_EL0_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P29 r v)

def _set_SPMACCESSR_EL1_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P29 r v)

def _set_SPMACCESSR_EL2_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P29 r v)

def _set_SPMACCESSR_EL3_Type_P29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P29 r v)

def _set_PMCNTENCLR_EL0_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P3 r v)

def _set_AMCNTENCLR0_EL0_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR0_EL0_Type_P3 r v)

def _set_AMCNTENCLR0_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR0_Type_P3 r v)

def _set_AMCNTENCLR1_EL0_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P3 r v)

def _set_AMCNTENCLR1_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P3 r v)

def _set_AMCNTENSET0_EL0_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET0_EL0_Type_P3 r v)

def _set_AMCNTENSET0_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET0_Type_P3 r v)

def _set_AMCNTENSET1_EL0_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P3 r v)

def _set_AMCNTENSET1_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P3 r v)

def _set_ICH_AP0R_EL2_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P3 r v)

def _set_ICH_AP0R_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P3 r v)

def _set_ICH_AP1R_EL2_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P3 r v)

def _set_ICH_AP1R_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P3 r v)

def _set_PMCNTENCLR_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P3 r v)

def _set_PMCNTENSET_EL0_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P3 r v)

def _set_PMCNTENSET_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P3 r v)

def _set_PMCNTEN_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P3 r v)

def _set_PMINTENCLR_EL1_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P3 r v)

def _set_PMINTENCLR_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P3 r v)

def _set_PMINTENSET_EL1_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P3 r v)

def _set_PMINTENSET_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P3 r v)

def _set_PMINTEN_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P3 r v)

def _set_PMOVSCLR_EL0_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P3 r v)

def _set_PMOVSR_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P3 r v)

def _set_PMOVSSET_EL0_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P3 r v)

def _set_PMOVSSET_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P3 r v)

def _set_PMOVS_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P3 r v)

def _set_PMSWINC_EL0_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P3 r v)

def _set_PMSWINC_Type_P3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P3 r v)

def _set_PMUACR_EL1_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P3 r v)

def _set_PMZR_EL0_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P3 r v)

def _set_SMPRIMAP_EL2_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P3 r v)

def _set_SPMACCESSR_EL1_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P3 r v)

def _set_SPMACCESSR_EL2_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P3 r v)

def _set_SPMACCESSR_EL3_Type_P3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P3 r v)

def _set_PMCNTENCLR_EL0_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P30 r v)

def _set_ICH_AP0R_EL2_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P30 r v)

def _set_ICH_AP0R_Type_P30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P30 r v)

def _set_ICH_AP1R_EL2_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P30 r v)

def _set_ICH_AP1R_Type_P30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P30 r v)

def _set_PMCNTENCLR_Type_P30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P30 r v)

def _set_PMCNTENSET_EL0_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P30 r v)

def _set_PMCNTENSET_Type_P30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P30 r v)

def _set_PMCNTEN_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P30 r v)

def _set_PMINTENCLR_EL1_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P30 r v)

def _set_PMINTENCLR_Type_P30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P30 r v)

def _set_PMINTENSET_EL1_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P30 r v)

def _set_PMINTENSET_Type_P30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P30 r v)

def _set_PMINTEN_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P30 r v)

def _set_PMOVSCLR_EL0_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P30 r v)

def _set_PMOVSR_Type_P30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P30 r v)

def _set_PMOVSSET_EL0_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P30 r v)

def _set_PMOVSSET_Type_P30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P30 r v)

def _set_PMOVS_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P30 r v)

def _set_PMSWINC_EL0_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P30 r v)

def _set_PMSWINC_Type_P30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P30 r v)

def _set_PMUACR_EL1_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P30 r v)

def _set_PMZR_EL0_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P30 r v)

def _set_SPMACCESSR_EL1_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P30 r v)

def _set_SPMACCESSR_EL2_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P30 r v)

def _set_SPMACCESSR_EL3_Type_P30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P30 r v)

def _set_PMCNTENCLR_EL0_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P4 r v)

def _set_AMCNTENCLR1_EL0_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P4 r v)

def _set_AMCNTENCLR1_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P4 r v)

def _set_AMCNTENSET1_EL0_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P4 r v)

def _set_AMCNTENSET1_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P4 r v)

def _set_ICH_AP0R_EL2_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P4 r v)

def _set_ICH_AP0R_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P4 r v)

def _set_ICH_AP1R_EL2_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P4 r v)

def _set_ICH_AP1R_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P4 r v)

def _set_PMCNTENCLR_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P4 r v)

def _set_PMCNTENSET_EL0_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P4 r v)

def _set_PMCNTENSET_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P4 r v)

def _set_PMCNTEN_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P4 r v)

def _set_PMINTENCLR_EL1_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P4 r v)

def _set_PMINTENCLR_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P4 r v)

def _set_PMINTENSET_EL1_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P4 r v)

def _set_PMINTENSET_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P4 r v)

def _set_PMINTEN_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P4 r v)

def _set_PMOVSCLR_EL0_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P4 r v)

def _set_PMOVSR_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P4 r v)

def _set_PMOVSSET_EL0_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P4 r v)

def _set_PMOVSSET_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P4 r v)

def _set_PMOVS_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P4 r v)

def _set_PMSWINC_EL0_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P4 r v)

def _set_PMSWINC_Type_P4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P4 r v)

def _set_PMUACR_EL1_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P4 r v)

def _set_PMZR_EL0_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P4 r v)

def _set_SMPRIMAP_EL2_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P4 r v)

def _set_SPMACCESSR_EL1_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P4 r v)

def _set_SPMACCESSR_EL2_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P4 r v)

def _set_SPMACCESSR_EL3_Type_P4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P4 r v)

def _set_PMCNTENCLR_EL0_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P5 r v)

def _set_AMCNTENCLR1_EL0_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P5 r v)

def _set_AMCNTENCLR1_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P5 r v)

def _set_AMCNTENSET1_EL0_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P5 r v)

def _set_AMCNTENSET1_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P5 r v)

def _set_ICH_AP0R_EL2_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P5 r v)

def _set_ICH_AP0R_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P5 r v)

def _set_ICH_AP1R_EL2_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P5 r v)

def _set_ICH_AP1R_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P5 r v)

def _set_PMCNTENCLR_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P5 r v)

def _set_PMCNTENSET_EL0_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P5 r v)

def _set_PMCNTENSET_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P5 r v)

def _set_PMCNTEN_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P5 r v)

def _set_PMINTENCLR_EL1_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P5 r v)

def _set_PMINTENCLR_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P5 r v)

def _set_PMINTENSET_EL1_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P5 r v)

def _set_PMINTENSET_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P5 r v)

def _set_PMINTEN_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P5 r v)

def _set_PMOVSCLR_EL0_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P5 r v)

def _set_PMOVSR_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P5 r v)

def _set_PMOVSSET_EL0_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P5 r v)

def _set_PMOVSSET_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P5 r v)

def _set_PMOVS_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P5 r v)

def _set_PMSWINC_EL0_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P5 r v)

def _set_PMSWINC_Type_P5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P5 r v)

def _set_PMUACR_EL1_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P5 r v)

def _set_PMZR_EL0_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P5 r v)

def _set_SMPRIMAP_EL2_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P5 r v)

def _set_SPMACCESSR_EL1_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P5 r v)

def _set_SPMACCESSR_EL2_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P5 r v)

def _set_SPMACCESSR_EL3_Type_P5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P5 r v)

def _set_PMCNTENCLR_EL0_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P6 r v)

def _set_AMCNTENCLR1_EL0_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P6 r v)

def _set_AMCNTENCLR1_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P6 r v)

def _set_AMCNTENSET1_EL0_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P6 r v)

def _set_AMCNTENSET1_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P6 r v)

def _set_ICH_AP0R_EL2_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P6 r v)

def _set_ICH_AP0R_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P6 r v)

def _set_ICH_AP1R_EL2_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P6 r v)

def _set_ICH_AP1R_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P6 r v)

def _set_PMCNTENCLR_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P6 r v)

def _set_PMCNTENSET_EL0_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P6 r v)

def _set_PMCNTENSET_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P6 r v)

def _set_PMCNTEN_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P6 r v)

def _set_PMINTENCLR_EL1_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P6 r v)

def _set_PMINTENCLR_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P6 r v)

def _set_PMINTENSET_EL1_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P6 r v)

def _set_PMINTENSET_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P6 r v)

def _set_PMINTEN_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P6 r v)

def _set_PMOVSCLR_EL0_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P6 r v)

def _set_PMOVSR_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P6 r v)

def _set_PMOVSSET_EL0_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P6 r v)

def _set_PMOVSSET_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P6 r v)

def _set_PMOVS_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P6 r v)

def _set_PMSWINC_EL0_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P6 r v)

def _set_PMSWINC_Type_P6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P6 r v)

def _set_PMUACR_EL1_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P6 r v)

def _set_PMZR_EL0_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P6 r v)

def _set_SMPRIMAP_EL2_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P6 r v)

def _set_SPMACCESSR_EL1_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P6 r v)

def _set_SPMACCESSR_EL2_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P6 r v)

def _set_SPMACCESSR_EL3_Type_P6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P6 r v)

def _set_PMCNTENCLR_EL0_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P7 r v)

def _set_AMCNTENCLR1_EL0_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P7 r v)

def _set_AMCNTENCLR1_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P7 r v)

def _set_AMCNTENSET1_EL0_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P7 r v)

def _set_AMCNTENSET1_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P7 r v)

def _set_ICH_AP0R_EL2_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P7 r v)

def _set_ICH_AP0R_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P7 r v)

def _set_ICH_AP1R_EL2_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P7 r v)

def _set_ICH_AP1R_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P7 r v)

def _set_PMCNTENCLR_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P7 r v)

def _set_PMCNTENSET_EL0_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P7 r v)

def _set_PMCNTENSET_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P7 r v)

def _set_PMCNTEN_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P7 r v)

def _set_PMINTENCLR_EL1_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P7 r v)

def _set_PMINTENCLR_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P7 r v)

def _set_PMINTENSET_EL1_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P7 r v)

def _set_PMINTENSET_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P7 r v)

def _set_PMINTEN_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P7 r v)

def _set_PMOVSCLR_EL0_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P7 r v)

def _set_PMOVSR_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P7 r v)

def _set_PMOVSSET_EL0_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P7 r v)

def _set_PMOVSSET_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P7 r v)

def _set_PMOVS_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P7 r v)

def _set_PMSWINC_EL0_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P7 r v)

def _set_PMSWINC_Type_P7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P7 r v)

def _set_PMUACR_EL1_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P7 r v)

def _set_PMZR_EL0_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P7 r v)

def _set_SMPRIMAP_EL2_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P7 r v)

def _set_SPMACCESSR_EL1_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P7 r v)

def _set_SPMACCESSR_EL2_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P7 r v)

def _set_SPMACCESSR_EL3_Type_P7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P7 r v)

def _set_PMCNTENCLR_EL0_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P8 r v)

def _set_AMCNTENCLR1_EL0_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P8 r v)

def _set_AMCNTENCLR1_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P8 r v)

def _set_AMCNTENSET1_EL0_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P8 r v)

def _set_AMCNTENSET1_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P8 r v)

def _set_ICH_AP0R_EL2_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P8 r v)

def _set_ICH_AP0R_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P8 r v)

def _set_ICH_AP1R_EL2_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P8 r v)

def _set_ICH_AP1R_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P8 r v)

def _set_PMCNTENCLR_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P8 r v)

def _set_PMCNTENSET_EL0_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P8 r v)

def _set_PMCNTENSET_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P8 r v)

def _set_PMCNTEN_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P8 r v)

def _set_PMINTENCLR_EL1_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P8 r v)

def _set_PMINTENCLR_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P8 r v)

def _set_PMINTENSET_EL1_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P8 r v)

def _set_PMINTENSET_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P8 r v)

def _set_PMINTEN_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P8 r v)

def _set_PMOVSCLR_EL0_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P8 r v)

def _set_PMOVSR_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P8 r v)

def _set_PMOVSSET_EL0_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P8 r v)

def _set_PMOVSSET_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P8 r v)

def _set_PMOVS_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P8 r v)

def _set_PMSWINC_EL0_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P8 r v)

def _set_PMSWINC_Type_P8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P8 r v)

def _set_PMUACR_EL1_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P8 r v)

def _set_PMZR_EL0_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P8 r v)

def _set_SMPRIMAP_EL2_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P8 r v)

def _set_SPMACCESSR_EL1_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P8 r v)

def _set_SPMACCESSR_EL2_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P8 r v)

def _set_SPMACCESSR_EL3_Type_P8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P8 r v)

def _set_PMCNTENCLR_EL0_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P9 r v)

def _set_AMCNTENCLR1_EL0_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P9 r v)

def _set_AMCNTENCLR1_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P9 r v)

def _set_AMCNTENSET1_EL0_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_P9 r v)

def _set_AMCNTENSET1_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCNTENSET1_Type_P9 r v)

def _set_ICH_AP0R_EL2_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P9 r v)

def _set_ICH_AP0R_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P9 r v)

def _set_ICH_AP1R_EL2_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P9 r v)

def _set_ICH_AP1R_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P9 r v)

def _set_PMCNTENCLR_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENCLR_Type_P9 r v)

def _set_PMCNTENSET_EL0_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_P9 r v)

def _set_PMCNTENSET_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTENSET_Type_P9 r v)

def _set_PMCNTEN_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCNTEN_Type_P9 r v)

def _set_PMINTENCLR_EL1_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_P9 r v)

def _set_PMINTENCLR_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENCLR_Type_P9 r v)

def _set_PMINTENSET_EL1_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_P9 r v)

def _set_PMINTENSET_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTENSET_Type_P9 r v)

def _set_PMINTEN_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMINTEN_Type_P9 r v)

def _set_PMOVSCLR_EL0_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_P9 r v)

def _set_PMOVSR_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_P9 r v)

def _set_PMOVSSET_EL0_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_P9 r v)

def _set_PMOVSSET_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_P9 r v)

def _set_PMOVS_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVS_Type_P9 r v)

def _set_PMSWINC_EL0_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_EL0_Type_P9 r v)

def _set_PMSWINC_Type_P9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSWINC_Type_P9 r v)

def _set_PMUACR_EL1_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUACR_EL1_Type_P9 r v)

def _set_PMZR_EL0_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMZR_EL0_Type_P9 r v)

def _set_SMPRIMAP_EL2_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMPRIMAP_EL2_Type_P9 r v)

def _set_SPMACCESSR_EL1_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P9 r v)

def _set_SPMACCESSR_EL2_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P9 r v)

def _set_SPMACCESSR_EL3_Type_P9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P9 r v)

def _set_PMCR_EL0_Type_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_D r v)

def _set_DBGVCR32_EL2_Type_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_D r v)

def _set_DBGVCR_Type_D (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_D r v)

def _set_DSPSR_EL0_Type_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_D r v)

def _set_PMCR_Type_D (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_D r v)

def _set_SPSR_EL1_Type_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_D r v)

def _set_SPSR_EL2_Type_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_D r v)

def _set_SPSR_EL3_Type_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_D r v)

def _set_PMCR_EL0_Type_DP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_DP r v)

def _set_ID_AA64ISAR0_EL1_Type_DP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_DP r v)

def _set_ID_ISAR6_EL1_Type_DP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_DP r v)

def _set_ID_ISAR6_Type_DP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_Type_DP r v)

def _set_PMCR_Type_DP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_DP r v)

def _set_PMCR_EL0_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_E r v)

def _set_DBGBCR_EL1_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_E r v)

def _set_DBGBCR_Type_E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_Type_E r v)

def _set_DBGWCR_EL1_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_E r v)

def _set_DBGWCR_Type_E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_Type_E r v)

def _set_DSPSR_EL0_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_E r v)

def _set_DSPSR_Type_E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_E r v)

def _set_PMBLIMITR_EL1_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBLIMITR_EL1_Type_E r v)

def _set_PMCR_Type_E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_E r v)

def _set_SPSR_EL1_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_E r v)

def _set_SPSR_EL2_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_E r v)

def _set_SPSR_EL3_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_E r v)

def _set_SPSR_abt_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_E r v)

def _set_SPSR_fiq_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_E r v)

def _set_SPSR_hyp_Type_E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_E r v)

def _set_SPSR_irq_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_E r v)

def _set_SPSR_mon_Type_E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_E r v)

def _set_SPSR_svc_Type_E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_E r v)

def _set_SPSR_und_Type_E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_E r v)

def _set_PMCR_EL0_Type_FZO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_FZO r v)

def _set_PMCFGR_Type_FZO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_FZO r v)

def _set_PMCR_Type_FZO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_FZO r v)

def _set_PMCR_EL0_Type_FZS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_FZS r v)

def _set_PMCR_EL0_Type_IDCODE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_IDCODE r v)

def _set_PMCR_Type_IDCODE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_IDCODE r v)

def _set_PMCR_EL0_Type_IMP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_IMP r v)

def _set_PMCR_Type_IMP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_IMP r v)

def _set_PMPCSCTL_Type_IMP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPCSCTL_Type_IMP r v)

def _set_TTBR0_Type_IMP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_Type_IMP r v)

def _set_TTBR1_Type_IMP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_Type_IMP r v)

def _set_PMCR_EL0_Type_LC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_LC r v)

def _set_PMCR_Type_LC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_LC r v)

def _set_PMCR_EL0_Type_LP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_LP r v)

def _set_PMCR_Type_LP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_LP r v)

def _set_PMCR_EL0_Type_P (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_P r v)

def _set_DBGVCR32_EL2_Type_P (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_P r v)

def _set_DBGVCR_Type_P (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_P r v)

def _set_PMBIDR_EL1_Type_P (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBIDR_EL1_Type_P r v)

def _set_PMCCFILTR_EL0_Type_P (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_P r v)

def _set_PMCCFILTR_Type_P (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_Type_P r v)

def _set_PMCR_Type_P (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_P r v)

def _set_PMEVTYPER_EL0_Type_P (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_P r v)

def _set_PMEVTYPER_Type_P (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_Type_P r v)

def _set_PMICFILTR_EL0_Type_P (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_P r v)

def _set_PMCR_EL0_Type_X (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_EL0_Type_X r v)

def _set_PMCR_Type_X (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCR_Type_X r v)

def _set_MDCR_EL3_Type_E3BREC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_E3BREC r v)

def _set_MDCR_EL3_Type_E3BREW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_E3BREW r v)

def _set_MDCR_EL3_Type_EDAD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_EDAD r v)

def _set_EDPRSR_Type_EDAD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_EDAD r v)

def _set_SDCR_Type_EDAD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDCR_Type_EDAD r v)

def _set_MDCR_EL3_Type_EDADE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_EDADE r v)

def _set_EDPRSR_Type_EDADE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_EDADE r v)

def _set_MDCR_EL3_Type_EPMAD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_EPMAD r v)

def _set_EDPRSR_Type_EPMAD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_EPMAD r v)

def _set_SDCR_Type_EPMAD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDCR_Type_EPMAD r v)

def _set_MDCR_EL3_Type_EPMADE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_EPMADE r v)

def _set_EDPRSR_Type_EPMADE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_EPMADE r v)

def _set_MDCR_EL3_Type_EPMSSAD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_EPMSSAD r v)

def _set_MDCR_EL3_Type_EnPM2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_EnPM2 r v)

def _set_MDCR_EL3_Type_EnPMS3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_EnPMS3 r v)

def _set_MDCR_EL3_Type_EnPMSN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_EnPMSN r v)

def _set_MDCR_EL3_Type_EnPMSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_EnPMSS r v)

def _set_MDCR_EL3_Type_MCCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_MCCD r v)

def _set_MDCR_EL3_Type_MPMX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_MPMX r v)

def _set_MDCR_EL3_Type_NSPB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_NSPB r v)

def _set_MDCR_EL3_Type_NSPBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_NSPBE r v)

def _set_MDCR_EL3_Type_RLTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_RLTE r v)

def _set_MDCR_EL3_Type_SBRBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_SBRBE r v)

def _set_MDCR_EL3_Type_SCCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_SCCD r v)

def _set_SDCR_Type_SCCD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDCR_Type_SCCD r v)

def _set_MDCR_EL3_Type_SPD32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_SPD32 r v)

def _set_MDCR_EL3_Type_SPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_SPME r v)

def _set_SDCR_Type_SPME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDCR_Type_SPME r v)

def _set_MDCR_EL3_Type_STE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCR_EL3_Type_STE r v)

def _set_SDCR_Type_STE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDCR_Type_STE r v)

def _set_PMCCFILTR_EL0_Type_NSH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_NSH r v)

def _set_PMCCFILTR_Type_NSH (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_Type_NSH r v)

def _set_PMEVTYPER_EL0_Type_NSH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_NSH r v)

def _set_PMEVTYPER_Type_NSH (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_Type_NSH r v)

def _set_PMICFILTR_EL0_Type_NSH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_NSH r v)

def _set_PMCCFILTR_EL0_Type_NSK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_NSK r v)

def _set_PMCCFILTR_Type_NSK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_Type_NSK r v)

def _set_PMEVTYPER_EL0_Type_NSK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_NSK r v)

def _set_PMEVTYPER_Type_NSK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_Type_NSK r v)

def _set_PMICFILTR_EL0_Type_NSK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_NSK r v)

def _set_PMCCFILTR_EL0_Type_NSU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_NSU r v)

def _set_DBGVCR32_EL2_Type_NSU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSU r v)

def _set_DBGVCR_Type_NSU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_NSU r v)

def _set_PMCCFILTR_Type_NSU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_Type_NSU r v)

def _set_PMEVTYPER_EL0_Type_NSU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_NSU r v)

def _set_PMEVTYPER_Type_NSU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_Type_NSU r v)

def _set_PMICFILTR_EL0_Type_NSU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_NSU r v)

def _set_PMCCFILTR_EL0_Type_RLH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_RLH r v)

def _set_PMEVTYPER_EL0_Type_RLH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_RLH r v)

def _set_PMICFILTR_EL0_Type_RLH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_RLH r v)

def _set_PMCCFILTR_EL0_Type_RLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_RLK r v)

def _set_PMEVTYPER_EL0_Type_RLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_RLK r v)

def _set_PMICFILTR_EL0_Type_RLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_RLK r v)

def _set_PMCCFILTR_EL0_Type_RLU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_RLU r v)

def _set_PMCCFILTR_Type_RLU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_Type_RLU r v)

def _set_PMEVTYPER_EL0_Type_RLU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_RLU r v)

def _set_PMEVTYPER_Type_RLU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_Type_RLU r v)

def _set_PMICFILTR_EL0_Type_RLU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_RLU r v)

def _set_PMCCFILTR_EL0_Type_SH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_SH r v)

def _set_GPCCR_EL3_Type_SH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPCCR_EL3_Type_SH r v)

def _set_PAR_EL1_Type_SH (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_SH r v)

def _set_PAR_Type_SH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_SH r v)

def _set_PMEVTYPER_EL0_Type_SH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_SH r v)

def _set_PMICFILTR_EL0_Type_SH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_SH r v)

def _set_PMCCFILTR_EL0_Type_U (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_EL0_Type_U r v)

def _set_DBGVCR32_EL2_Type_U (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_U r v)

def _set_DBGVCR_Type_U (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_U r v)

def _set_GICH_MISR_Type_U (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_MISR_Type_U r v)

def _set_ICH_MISR_EL2_Type_U (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_EL2_Type_U r v)

def _set_ICH_MISR_Type_U (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_Type_U r v)

def _set_MPIDR_EL1_Type_U (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_EL1_Type_U r v)

def _set_MPIDR_Type_U (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_Type_U r v)

def _set_PMCCFILTR_Type_U (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCFILTR_Type_U r v)

def _set_PMEVTYPER_EL0_Type_U (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_U r v)

def _set_PMEVTYPER_Type_U (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_Type_U r v)

def _set_PMICFILTR_EL0_Type_U (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_U r v)

def _set_VMPIDR_EL2_Type_U (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_U r v)

def _set_VMPIDR_Type_U (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_Type_U r v)

def _set_PMEVTYPER_EL0_Type_MT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_MT r v)

def _set_MPIDR_EL1_Type_MT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_EL1_Type_MT r v)

def _set_MPIDR_Type_MT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_Type_MT r v)

def _set_PMEVTYPER_Type_MT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_Type_MT r v)

def _set_VMPIDR_EL2_Type_MT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_MT r v)

def _set_VMPIDR_Type_MT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_Type_MT r v)

def _set_PMEVTYPER_EL0_Type_SYNC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_SYNC r v)

def _set_PMICFILTR_EL0_Type_SYNC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_SYNC r v)

def _set_PMEVTYPER_EL0_Type_TC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_TC r v)

def _set_ICH_HCR_EL2_Type_TC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_TC r v)

def _set_ICH_HCR_Type_TC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_TC r v)

def _set_PMEVTYPER_EL0_Type_TE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_TE r v)

def _set_HSCTLR_Type_TE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_TE r v)

def _set_SCTLR_Type_TE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_TE r v)

def _set_PMEVTYPER_EL0_Type_TH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_TH r v)

def _set_PMEVTYPER_EL0_Type_evtCount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_EL0_Type_evtCount r v)

def _set_AMEVTYPER0_EL0_Type_evtCount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVTYPER0_EL0_Type_evtCount r v)

def _set_AMEVTYPER0_Type_evtCount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVTYPER0_Type_evtCount r v)

def _set_AMEVTYPER1_EL0_Type_evtCount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVTYPER1_EL0_Type_evtCount r v)

def _set_AMEVTYPER1_Type_evtCount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVTYPER1_Type_evtCount r v)

def _set_PMEVTYPER_Type_evtCount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVTYPER_Type_evtCount r v)

def _set_PMICFILTR_EL0_Type_evtCount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_evtCount r v)

def _set_SDCR_Type_SPD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDCR_Type_SPD r v)

def _set_EDPRSR_Type_SPD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_SPD r v)

def _set_SDER32_EL2_Type_SUIDEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDER32_EL2_Type_SUIDEN r v)

def _set_SDER32_EL3_Type_SUIDEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDER32_EL3_Type_SUIDEN r v)

def _set_SDER_Type_SUIDEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDER_Type_SUIDEN r v)

def _set_SDER32_EL2_Type_SUNIDEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDER32_EL2_Type_SUNIDEN r v)

def _set_SDER32_EL3_Type_SUNIDEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDER32_EL3_Type_SUNIDEN r v)

def _set_SDER_Type_SUNIDEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SDER_Type_SUNIDEN r v)

def _set_PMICNTR_EL0_Type_ICNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICNTR_EL0_Type_ICNT r v)

def _set_PMICNTSVR_EL1_Type_ICNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMICNTSVR_EL1_Type_ICNT r v)

def _set_BRBCR_EL1_Type_E0BRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL1_Type_E0BRE r v)

def _set_BRBCR_EL1_Type_E1BRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL1_Type_E1BRE r v)

def _set_BRBCR_EL1_Type_ERTN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL1_Type_ERTN r v)

def _set_BRBCR_EL2_Type_ERTN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL2_Type_ERTN r v)

def _set_BRBCR_EL1_Type_EXCEPTION (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL1_Type_EXCEPTION r v)

def _set_BRBCR_EL2_Type_EXCEPTION (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL2_Type_EXCEPTION r v)

def _set_BRBCR_EL1_Type_FZP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL1_Type_FZP r v)

def _set_BRBCR_EL2_Type_FZP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL2_Type_FZP r v)

def _set_BRBCR_EL1_Type_FZPSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL1_Type_FZPSS r v)

def _set_BRBCR_EL2_Type_FZPSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL2_Type_FZPSS r v)

def _set_BRBCR_EL2_Type_E0HBRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL2_Type_E0HBRE r v)

def _set_BRBCR_EL2_Type_E2BRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBCR_EL2_Type_E2BRE r v)

def _set_BRBFCR_EL1_Type_BANK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_BANK r v)

def _set_MDSELR_EL1_Type_BANK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSELR_EL1_Type_BANK r v)

def _set_SPMSELR_EL0_Type_BANK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMSELR_EL0_Type_BANK r v)

def _set_BRBFCR_EL1_Type_CONDDIR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_CONDDIR r v)

def _set_BRBFCR_EL1_Type_DIRCALL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_DIRCALL r v)

def _set_BRBFCR_EL1_Type_DIRECT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_DIRECT r v)

def _set_BRBFCR_EL1_Type_EnI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_EnI r v)

def _set_BRBFCR_EL1_Type_INDCALL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_INDCALL r v)

def _set_BRBFCR_EL1_Type_INDIRECT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_INDIRECT r v)

def _set_BRBFCR_EL1_Type_PAUSED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_PAUSED r v)

def _set_BRBFCR_EL1_Type_RTN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_RTN r v)

def _set_CNTHCTL_EL2_Type_CNTPMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_CNTPMASK r v)

def _set_CNTHCTL_EL2_Type_CNTVMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_CNTVMASK r v)

def _set_CNTHCTL_EL2_Type_ECV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_ECV r v)

def _set_ID_AA64MMFR0_EL1_Type_ECV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_ECV r v)

def _set_CNTHCTL_EL2_Type_EL0PCTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL0PCTEN r v)

def _set_CNTEL0ACR_Type_EL0PCTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTEL0ACR_Type_EL0PCTEN r v)

def _set_CNTKCTL_EL1_Type_EL0PCTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EL0PCTEN r v)

def _set_CNTHCTL_EL2_Type_EL0PTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL0PTEN r v)

def _set_CNTEL0ACR_Type_EL0PTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTEL0ACR_Type_EL0PTEN r v)

def _set_CNTKCTL_EL1_Type_EL0PTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EL0PTEN r v)

def _set_CNTHCTL_EL2_Type_EL0VCTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL0VCTEN r v)

def _set_CNTEL0ACR_Type_EL0VCTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTEL0ACR_Type_EL0VCTEN r v)

def _set_CNTKCTL_EL1_Type_EL0VCTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EL0VCTEN r v)

def _set_CNTHCTL_EL2_Type_EL0VTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL0VTEN r v)

def _set_CNTEL0ACR_Type_EL0VTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTEL0ACR_Type_EL0VTEN r v)

def _set_CNTKCTL_EL1_Type_EL0VTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EL0VTEN r v)

def _set_CNTHCTL_EL2_Type_EL1NVPCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1NVPCT r v)

def _set_CNTHCTL_EL2_Type_EL1NVVCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1NVVCT r v)

def _set_CNTHCTL_EL2_Type_EL1PCEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1PCEN r v)

def _set_CNTHCTL_EL2_Type_EL1PTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1PTEN r v)

def _set_CNTHCTL_EL2_Type_EL1TVCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1TVCT r v)

def _set_CNTHCTL_EL2_Type_EL1TVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1TVT r v)

def _set_CNTHCTL_EL2_Type_EVNTDIR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EVNTDIR r v)

def _set_CNTHCTL_Type_EVNTDIR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_Type_EVNTDIR r v)

def _set_CNTKCTL_EL1_Type_EVNTDIR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EVNTDIR r v)

def _set_CNTKCTL_Type_EVNTDIR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_Type_EVNTDIR r v)

def _set_CNTHCTL_EL2_Type_EVNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EVNTEN r v)

def _set_CNTHCTL_Type_EVNTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_Type_EVNTEN r v)

def _set_CNTKCTL_EL1_Type_EVNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EVNTEN r v)

def _set_CNTKCTL_Type_EVNTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_Type_EVNTEN r v)

def _set_CNTHCTL_EL2_Type_EVNTI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EVNTI r v)

def _set_CNTHCTL_Type_EVNTI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_Type_EVNTI r v)

def _set_CNTKCTL_EL1_Type_EVNTI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EVNTI r v)

def _set_CNTKCTL_Type_EVNTI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_Type_EVNTI r v)

def _set_CNTHCTL_EL2_Type_EVNTIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EVNTIS r v)

def _set_CNTHCTL_Type_EVNTIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_Type_EVNTIS r v)

def _set_CNTKCTL_EL1_Type_EVNTIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EVNTIS r v)

def _set_CNTKCTL_Type_EVNTIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_Type_EVNTIS r v)

def _set_EDECR_Type_OSUCE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECR_Type_OSUCE r v)

def _set_CTIDEVCTL_Type_OSUCE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVCTL_Type_OSUCE r v)

def _set_EDECR_Type_PME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECR_Type_PME r v)

def _set_EDECR_Type_RCE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECR_Type_RCE r v)

def _set_CTIDEVCTL_Type_RCE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVCTL_Type_RCE r v)

def _set_EDECR_Type_SS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECR_Type_SS r v)

def _set_DBGVCR32_EL2_Type_SS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SS r v)

def _set_DBGVCR_Type_SS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_SS r v)

def _set_DSPSR_EL0_Type_SS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_SS r v)

def _set_DSPSR_Type_SS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_SS r v)

def _set_EDESR_Type_SS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDESR_Type_SS r v)

def _set_MDSCR_EL1_Type_SS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_SS r v)

def _set_PAR_Type_SS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_SS r v)

def _set_PMCFGR_Type_SS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_SS r v)

def _set_PMPCSCTL_Type_SS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPCSCTL_Type_SS r v)

def _set_PMSSCR_EL1_Type_SS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSSCR_EL1_Type_SS r v)

def _set_SPSR_EL1_Type_SS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_SS r v)

def _set_SPSR_EL2_Type_SS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_SS r v)

def _set_SPSR_EL3_Type_SS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_SS r v)

def _set_DSPSR_EL0_Type_ALLINT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_ALLINT r v)

def _set_SPSR_EL1_Type_ALLINT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_ALLINT r v)

def _set_SPSR_EL2_Type_ALLINT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_ALLINT r v)

def _set_SPSR_EL3_Type_ALLINT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_ALLINT r v)

def _set_DSPSR_EL0_Type_BTYPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_BTYPE r v)

def _set_SPSR_EL1_Type_BTYPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_BTYPE r v)

def _set_SPSR_EL2_Type_BTYPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_BTYPE r v)

def _set_SPSR_EL3_Type_BTYPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_BTYPE r v)

def _set_DSPSR_EL0_Type_DIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_DIT r v)

def _set_DSPSR_Type_DIT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_DIT r v)

def _set_ID_AA64PFR0_EL1_Type_DIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_DIT r v)

def _set_ID_PFR0_EL1_Type_DIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_DIT r v)

def _set_ID_PFR0_Type_DIT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_Type_DIT r v)

def _set_SPSR_EL1_Type_DIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_DIT r v)

def _set_SPSR_EL2_Type_DIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_DIT r v)

def _set_SPSR_EL3_Type_DIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_DIT r v)

def _set_SPSR_abt_Type_DIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_DIT r v)

def _set_SPSR_fiq_Type_DIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_DIT r v)

def _set_SPSR_hyp_Type_DIT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_DIT r v)

def _set_SPSR_irq_Type_DIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_DIT r v)

def _set_SPSR_mon_Type_DIT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_DIT r v)

def _set_SPSR_svc_Type_DIT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_DIT r v)

def _set_SPSR_und_Type_DIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_DIT r v)

def _set_DSPSR_EL0_Type_EXLOCK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_EXLOCK r v)

def _set_SPSR_EL1_Type_EXLOCK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_EXLOCK r v)

def _set_SPSR_EL2_Type_EXLOCK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_EXLOCK r v)

def _set_SPSR_EL3_Type_EXLOCK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_EXLOCK r v)

def _set_DSPSR_EL0_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_F r v)

def _set_DBGVCR32_EL2_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_F r v)

def _set_DBGVCR_Type_F (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_F r v)

def _set_DSPSR_Type_F (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_F r v)

def _set_ISR_EL1_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ISR_EL1_Type_F r v)

def _set_ISR_Type_F (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ISR_Type_F r v)

def _set_PAR_EL1_Type_F (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_F r v)

def _set_PAR_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_F r v)

def _set_PMBIDR_EL1_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBIDR_EL1_Type_F r v)

def _set_SPSR_EL1_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_F r v)

def _set_SPSR_EL2_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_F r v)

def _set_SPSR_EL3_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_F r v)

def _set_SPSR_abt_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_F r v)

def _set_SPSR_fiq_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_F r v)

def _set_SPSR_hyp_Type_F (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_F r v)

def _set_SPSR_irq_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_F r v)

def _set_SPSR_mon_Type_F (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_F r v)

def _set_SPSR_svc_Type_F (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_F r v)

def _set_SPSR_und_Type_F (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_F r v)

def _set_DSPSR_EL0_Type_GE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_GE r v)

def _set_DSPSR_Type_GE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_GE r v)

def _set_SPSR_EL1_Type_GE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_GE r v)

def _set_SPSR_EL2_Type_GE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_GE r v)

def _set_SPSR_EL3_Type_GE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_GE r v)

def _set_SPSR_abt_Type_GE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_GE r v)

def _set_SPSR_fiq_Type_GE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_GE r v)

def _set_SPSR_hyp_Type_GE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_GE r v)

def _set_SPSR_irq_Type_GE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_GE r v)

def _set_SPSR_mon_Type_GE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_GE r v)

def _set_SPSR_svc_Type_GE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_GE r v)

def _set_SPSR_und_Type_GE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_GE r v)

def _set_DSPSR_EL0_Type_IT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_IT r v)

def _set_DSPSR_Type_IT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_IT r v)

def _set_SPSR_EL1_Type_IT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_IT r v)

def _set_SPSR_EL2_Type_IT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_IT r v)

def _set_SPSR_EL3_Type_IT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_IT r v)

def _set_SPSR_abt_Type_IT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_IT r v)

def _set_SPSR_fiq_Type_IT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_IT r v)

def _set_SPSR_hyp_Type_IT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_IT r v)

def _set_SPSR_irq_Type_IT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_IT r v)

def _set_SPSR_mon_Type_IT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_IT r v)

def _set_SPSR_svc_Type_IT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_IT r v)

def _set_SPSR_und_Type_IT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_IT r v)

def _set_DSPSR_EL0_Type_PAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_PAN r v)

def _set_DSPSR_Type_PAN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_PAN r v)

def _set_ID_AA64MMFR1_EL1_Type_PAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_PAN r v)

def _set_ID_MMFR3_EL1_Type_PAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_EL1_Type_PAN r v)

def _set_ID_MMFR3_Type_PAN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_Type_PAN r v)

def _set_SPSR_EL1_Type_PAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_PAN r v)

def _set_SPSR_EL2_Type_PAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_PAN r v)

def _set_SPSR_EL3_Type_PAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_PAN r v)

def _set_SPSR_abt_Type_PAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_PAN r v)

def _set_SPSR_fiq_Type_PAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_PAN r v)

def _set_SPSR_hyp_Type_PAN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_PAN r v)

def _set_SPSR_irq_Type_PAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_PAN r v)

def _set_SPSR_mon_Type_PAN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_PAN r v)

def _set_SPSR_svc_Type_PAN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_PAN r v)

def _set_SPSR_und_Type_PAN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_PAN r v)

def _set_DSPSR_EL0_Type_PM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_PM r v)

def _set_SPSR_EL1_Type_PM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_PM r v)

def _set_SPSR_EL2_Type_PM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_PM r v)

def _set_SPSR_EL3_Type_PM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_PM r v)

def _set_DSPSR_EL0_Type_PPEND (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_PPEND r v)

def _set_DSPSR2_Type_PPEND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR2_Type_PPEND r v)

def _set_SPSR_EL1_Type_PPEND (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_PPEND r v)

def _set_SPSR_EL2_Type_PPEND (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_PPEND r v)

def _set_SPSR_EL3_Type_PPEND (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_PPEND r v)

def _set_DSPSR_EL0_Type_Q (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_Q r v)

def _set_DSPSR_Type_Q (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_Q r v)

def _set_SPSR_EL1_Type_Q (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_Q r v)

def _set_SPSR_EL2_Type_Q (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_Q r v)

def _set_SPSR_EL3_Type_Q (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_Q r v)

def _set_SPSR_abt_Type_Q (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_Q r v)

def _set_SPSR_fiq_Type_Q (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_Q r v)

def _set_SPSR_hyp_Type_Q (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_Q r v)

def _set_SPSR_irq_Type_Q (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_Q r v)

def _set_SPSR_mon_Type_Q (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_Q r v)

def _set_SPSR_svc_Type_Q (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_Q r v)

def _set_SPSR_und_Type_Q (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_Q r v)

def _set_DSPSR_EL0_Type_TCO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_TCO r v)

def _set_SPSR_EL1_Type_TCO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_TCO r v)

def _set_SPSR_EL2_Type_TCO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_TCO r v)

def _set_SPSR_EL3_Type_TCO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_TCO r v)

def _set_DSPSR_EL0_Type_UAO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_EL0_Type_UAO r v)

def _set_ID_AA64MMFR2_EL1_Type_UAO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_UAO r v)

def _set_SPSR_EL1_Type_UAO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL1_Type_UAO r v)

def _set_SPSR_EL2_Type_UAO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL2_Type_UAO r v)

def _set_SPSR_EL3_Type_UAO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_EL3_Type_UAO r v)

def _set_DSPSR_Type_SSBS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DSPSR_Type_SSBS r v)

def _set_ID_AA64PFR1_EL1_Type_SSBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_SSBS r v)

def _set_ID_PFR2_EL1_Type_SSBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR2_EL1_Type_SSBS r v)

def _set_ID_PFR2_Type_SSBS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR2_Type_SSBS r v)

def _set_SPSR_abt_Type_SSBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_SSBS r v)

def _set_SPSR_fiq_Type_SSBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_SSBS r v)

def _set_SPSR_hyp_Type_SSBS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_SSBS r v)

def _set_SPSR_irq_Type_SSBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_SSBS r v)

def _set_SPSR_mon_Type_SSBS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_SSBS r v)

def _set_SPSR_svc_Type_SSBS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_SSBS r v)

def _set_SPSR_und_Type_SSBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_SSBS r v)

def _set_TCR_EL1_Type_A1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_A1 r v)

def _set_TCR_EL2_Type_A1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_A1 r v)

def _set_TTBCR_Type_A1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_A1 r v)

def _set_TCR_EL1_Type_AS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_AS r v)

def _set_TCR_EL2_Type_AS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_AS r v)

def _set_TCR_EL1_Type_DS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_DS r v)

def _set_GICD_CTLR_Type_DS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_DS r v)

def _set_LORC_EL1_Type_DS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORC_EL1_Type_DS r v)

def _set_TCR_EL3_Type_DS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_DS r v)

def _set_VTCR_EL2_Type_DS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_DS r v)

def _set_TCR_EL1_Type_E0PD0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_E0PD0 r v)

def _set_TCR_EL2_Type_E0PD0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_E0PD0 r v)

def _set_TCR_EL1_Type_E0PD1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_E0PD1 r v)

def _set_TCR_EL2_Type_E0PD1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_E0PD1 r v)

def _set_TCR_EL1_Type_EPD0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_EPD0 r v)

def _set_TCR_EL2_Type_EPD0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_EPD0 r v)

def _set_TTBCR_Type_EPD0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_EPD0 r v)

def _set_TCR_EL1_Type_EPD1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_EPD1 r v)

def _set_TCR_EL2_Type_EPD1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_EPD1 r v)

def _set_TTBCR_Type_EPD1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_EPD1 r v)

def _set_TCR_EL1_Type_HA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HA r v)

def _set_TCR_EL3_Type_HA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_HA r v)

def _set_VTCR_EL2_Type_HA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_HA r v)

def _set_TCR_EL1_Type_HD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HD r v)

def _set_TCR_EL3_Type_HD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_HD r v)

def _set_VTCR_EL2_Type_HD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_HD r v)

def _set_TCR_EL1_Type_HPD0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HPD0 r v)

def _set_TCR_EL2_Type_HPD0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HPD0 r v)

def _set_TTBCR2_Type_HPD0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_HPD0 r v)

def _set_TCR_EL1_Type_HPD1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HPD1 r v)

def _set_TCR_EL2_Type_HPD1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HPD1 r v)

def _set_TTBCR2_Type_HPD1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_HPD1 r v)

def _set_TCR_EL1_Type_HWU059 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HWU059 r v)

def _set_TCR_EL2_Type_HWU059 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU059 r v)

def _set_TTBCR2_Type_HWU059 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_HWU059 r v)

def _set_TCR_EL1_Type_HWU060 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HWU060 r v)

def _set_TCR_EL2_Type_HWU060 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU060 r v)

def _set_TTBCR2_Type_HWU060 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_HWU060 r v)

def _set_TCR_EL1_Type_HWU061 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HWU061 r v)

def _set_TCR_EL2_Type_HWU061 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU061 r v)

def _set_TTBCR2_Type_HWU061 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_HWU061 r v)

def _set_TCR_EL1_Type_HWU062 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HWU062 r v)

def _set_TCR_EL2_Type_HWU062 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU062 r v)

def _set_TTBCR2_Type_HWU062 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_HWU062 r v)

def _set_TCR_EL1_Type_HWU159 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HWU159 r v)

def _set_TCR_EL2_Type_HWU159 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU159 r v)

def _set_TTBCR2_Type_HWU159 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_HWU159 r v)

def _set_TCR_EL1_Type_HWU160 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HWU160 r v)

def _set_TCR_EL2_Type_HWU160 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU160 r v)

def _set_TTBCR2_Type_HWU160 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_HWU160 r v)

def _set_TCR_EL1_Type_HWU161 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HWU161 r v)

def _set_TCR_EL2_Type_HWU161 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU161 r v)

def _set_TTBCR2_Type_HWU161 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_HWU161 r v)

def _set_TCR_EL1_Type_HWU162 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_HWU162 r v)

def _set_TCR_EL2_Type_HWU162 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU162 r v)

def _set_TTBCR2_Type_HWU162 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR2_Type_HWU162 r v)

def _set_TCR_EL1_Type_IPS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_IPS r v)

def _set_TCR_EL2_Type_IPS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_IPS r v)

def _set_TCR_EL1_Type_IRGN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_IRGN0 r v)

def _set_HTCR_Type_IRGN0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTCR_Type_IRGN0 r v)

def _set_TCR_EL2_Type_IRGN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_IRGN0 r v)

def _set_TCR_EL3_Type_IRGN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_IRGN0 r v)

def _set_TTBCR_Type_IRGN0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_IRGN0 r v)

def _set_VTCR_EL2_Type_IRGN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_IRGN0 r v)

def _set_VTCR_Type_IRGN0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_IRGN0 r v)

def _set_TCR_EL1_Type_IRGN1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_IRGN1 r v)

def _set_TCR_EL2_Type_IRGN1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_IRGN1 r v)

def _set_TTBCR_Type_IRGN1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_IRGN1 r v)

def _set_TCR_EL1_Type_MTX0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_MTX0 r v)

def _set_TCR_EL2_Type_MTX0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_MTX0 r v)

def _set_TCR_EL1_Type_MTX1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_MTX1 r v)

def _set_TCR_EL2_Type_MTX1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_MTX1 r v)

def _set_TCR_EL1_Type_NFD0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_NFD0 r v)

def _set_TCR_EL2_Type_NFD0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_NFD0 r v)

def _set_TCR_EL1_Type_NFD1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_NFD1 r v)

def _set_TCR_EL2_Type_NFD1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_NFD1 r v)

def _set_TCR_EL1_Type_ORGN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_ORGN0 r v)

def _set_HTCR_Type_ORGN0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTCR_Type_ORGN0 r v)

def _set_TCR_EL2_Type_ORGN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_ORGN0 r v)

def _set_TCR_EL3_Type_ORGN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_ORGN0 r v)

def _set_TTBCR_Type_ORGN0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_ORGN0 r v)

def _set_VTCR_EL2_Type_ORGN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_ORGN0 r v)

def _set_VTCR_Type_ORGN0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_ORGN0 r v)

def _set_TCR_EL1_Type_ORGN1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_ORGN1 r v)

def _set_TCR_EL2_Type_ORGN1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_ORGN1 r v)

def _set_TTBCR_Type_ORGN1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_ORGN1 r v)

def _set_TCR_EL1_Type_SH0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_SH0 r v)

def _set_HTCR_Type_SH0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTCR_Type_SH0 r v)

def _set_TCR_EL2_Type_SH0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_SH0 r v)

def _set_TCR_EL3_Type_SH0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_SH0 r v)

def _set_TTBCR_Type_SH0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_SH0 r v)

def _set_VTCR_EL2_Type_SH0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_SH0 r v)

def _set_VTCR_Type_SH0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_SH0 r v)

def _set_TCR_EL1_Type_SH1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_SH1 r v)

def _set_TCR_EL2_Type_SH1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_SH1 r v)

def _set_TTBCR_Type_SH1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_SH1 r v)

def _set_TCR_EL1_Type_T0SZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_T0SZ r v)

def _set_HTCR_Type_T0SZ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTCR_Type_T0SZ r v)

def _set_TCR_EL2_Type_T0SZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_T0SZ r v)

def _set_TCR_EL3_Type_T0SZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_T0SZ r v)

def _set_TTBCR_Type_T0SZ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_T0SZ r v)

def _set_VSTCR_EL2_Type_T0SZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSTCR_EL2_Type_T0SZ r v)

def _set_VTCR_EL2_Type_T0SZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_T0SZ r v)

def _set_VTCR_Type_T0SZ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_T0SZ r v)

def _set_TCR_EL1_Type_T1SZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_T1SZ r v)

def _set_TCR_EL2_Type_T1SZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_T1SZ r v)

def _set_TTBCR_Type_T1SZ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_T1SZ r v)

def _set_TCR_EL1_Type_TBI0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_TBI0 r v)

def _set_TCR_EL2_Type_TBI0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TBI0 r v)

def _set_TCR_EL1_Type_TBI1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_TBI1 r v)

def _set_TCR_EL2_Type_TBI1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TBI1 r v)

def _set_TCR_EL1_Type_TBID0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_TBID0 r v)

def _set_TCR_EL2_Type_TBID0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TBID0 r v)

def _set_TCR_EL1_Type_TBID1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_TBID1 r v)

def _set_TCR_EL2_Type_TBID1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TBID1 r v)

def _set_TCR_EL1_Type_TCMA0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_TCMA0 r v)

def _set_TCR_EL2_Type_TCMA0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TCMA0 r v)

def _set_TCR_EL1_Type_TCMA1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_TCMA1 r v)

def _set_TCR_EL2_Type_TCMA1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TCMA1 r v)

def _set_TCR_EL1_Type_TG0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_TG0 r v)

def _set_TCR_EL2_Type_TG0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TG0 r v)

def _set_TCR_EL3_Type_TG0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_TG0 r v)

def _set_VSTCR_EL2_Type_TG0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSTCR_EL2_Type_TG0 r v)

def _set_VTCR_EL2_Type_TG0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_TG0 r v)

def _set_TCR_EL1_Type_TG1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL1_Type_TG1 r v)

def _set_TCR_EL2_Type_TG1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TG1 r v)

def _set_TCR_EL2_Type_HPD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HPD r v)

def _set_HTCR_Type_HPD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTCR_Type_HPD r v)

def _set_TCR_EL3_Type_HPD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_HPD r v)

def _set_TCR_EL2_Type_HWU59 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU59 r v)

def _set_HTCR_Type_HWU59 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTCR_Type_HWU59 r v)

def _set_TCR_EL3_Type_HWU59 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_HWU59 r v)

def _set_VTCR_EL2_Type_HWU59 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_HWU59 r v)

def _set_VTCR_Type_HWU59 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_HWU59 r v)

def _set_TCR_EL2_Type_HWU60 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU60 r v)

def _set_HTCR_Type_HWU60 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTCR_Type_HWU60 r v)

def _set_TCR_EL3_Type_HWU60 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_HWU60 r v)

def _set_VTCR_EL2_Type_HWU60 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_HWU60 r v)

def _set_VTCR_Type_HWU60 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_HWU60 r v)

def _set_TCR_EL2_Type_HWU61 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU61 r v)

def _set_HTCR_Type_HWU61 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTCR_Type_HWU61 r v)

def _set_TCR_EL3_Type_HWU61 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_HWU61 r v)

def _set_VTCR_EL2_Type_HWU61 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_HWU61 r v)

def _set_VTCR_Type_HWU61 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_HWU61 r v)

def _set_TCR_EL2_Type_HWU62 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_HWU62 r v)

def _set_HTCR_Type_HWU62 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTCR_Type_HWU62 r v)

def _set_TCR_EL3_Type_HWU62 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_HWU62 r v)

def _set_VTCR_EL2_Type_HWU62 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_HWU62 r v)

def _set_VTCR_Type_HWU62 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_HWU62 r v)

def _set_TCR_EL2_Type_MTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_MTX r v)

def _set_TCR_EL3_Type_MTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_MTX r v)

def _set_TCR_EL2_Type_PS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_PS r v)

def _set_TCR_EL3_Type_PS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_PS r v)

def _set_VTCR_EL2_Type_PS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_PS r v)

def _set_TCR_EL2_Type_TBI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TBI r v)

def _set_TCR_EL3_Type_TBI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_TBI r v)

def _set_TCR_EL2_Type_TBID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TBID r v)

def _set_TCR_EL3_Type_TBID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_TBID r v)

def _set_TCR_EL2_Type_TCMA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL2_Type_TCMA r v)

def _set_TCR_EL3_Type_TCMA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_TCMA r v)

def _set_TCR_EL3_Type_AIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_AIE r v)

def _set_ID_AA64MMFR3_EL1_Type_AIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_AIE r v)

def _set_TCR2_EL1_Type_AIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_AIE r v)

def _set_TCR2_EL2_Type_AIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_AIE r v)

def _set_TCR_EL3_Type_D128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_D128 r v)

def _set_ID_AA64MMFR3_EL1_Type_D128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_D128 r v)

def _set_PAR_EL1_Type_D128 (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_D128 r v)

def _set_TCR2_EL1_Type_D128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_D128 r v)

def _set_TCR2_EL2_Type_D128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_D128 r v)

def _set_VTCR_EL2_Type_D128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_D128 r v)

def _set_TCR_EL3_Type_DisCH0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_DisCH0 r v)

def _set_TCR2_EL1_Type_DisCH0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_DisCH0 r v)

def _set_TCR2_EL2_Type_DisCH0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_DisCH0 r v)

def _set_TCR_EL3_Type_HAFT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_HAFT r v)

def _set_TCR2_EL1_Type_HAFT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_HAFT r v)

def _set_TCR2_EL2_Type_HAFT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_HAFT r v)

def _set_VTCR_EL2_Type_HAFT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_HAFT r v)

def _set_TCR_EL3_Type_PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_PIE r v)

def _set_TCR2_EL1_Type_PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_PIE r v)

def _set_TCR2_EL2_Type_PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_PIE r v)

def _set_TCR_EL3_Type_POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_POE r v)

def _set_TCR2_EL1_Type_POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_POE r v)

def _set_TCR2_EL2_Type_POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_POE r v)

def _set_TCR_EL3_Type_PTTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_PTTWI r v)

def _set_HCRX_EL2_Type_PTTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_PTTWI r v)

def _set_TCR2_EL1_Type_PTTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_PTTWI r v)

def _set_TCR2_EL2_Type_PTTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_PTTWI r v)

def _set_TCR_EL3_Type_PnCH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR_EL3_Type_PnCH r v)

def _set_TCR2_EL1_Type_PnCH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_PnCH r v)

def _set_TCR2_EL2_Type_PnCH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_PnCH r v)

/-- Type quantifiers: n : Int -/
def R_read (n : Int) : SailM (BitVec 32) := do
  let offset ← (( do (undefined_int ()) ) : SailM Int )
  if ((n == 15) : Bool)
  then
    (do
      let offset ← do
        if ((BEq.beq (← (CurrentInstrSet ())) InstrSet_A32) : Bool)
        then (pure 8)
        else (pure 4)
      (pure (BitVec.addInt (Sail.BitVec.extractLsb (← readReg _PC) 31 0) offset)))
  else (Rmode_read n (← readReg PSTATE).M)

def _set_BRBIDR0_EL1_Type_FORMAT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBIDR0_EL1_Type_FORMAT r v)

def _set_BRBIDR0_EL1_Type_NUMREC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_BRBIDR0_EL1_Type_NUMREC r v)

def _set_PMSIDR_EL1_Type_ArchInst (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_ArchInst r v)

def _set_PMSIDR_EL1_Type_CRR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_CRR r v)

def _set_PMSIDR_EL1_Type_CountSize (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_CountSize r v)

def _set_PMSIDR_EL1_Type_ERnd (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_ERnd r v)

def _set_PMSIDR_EL1_Type_FDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_FDS r v)

def _set_PMSFCR_EL1_Type_FDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_FDS r v)

def _set_PMSIDR_EL1_Type_FE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_FE r v)

def _set_PMSFCR_EL1_Type_FE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_FE r v)

def _set_PMSIDR_EL1_Type_FL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_FL r v)

def _set_PMSFCR_EL1_Type_FL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_FL r v)

def _set_PMSIDR_EL1_Type_FT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_FT r v)

def _set_PMSFCR_EL1_Type_FT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_FT r v)

def _set_PMSIDR_EL1_Type_FnE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_FnE r v)

def _set_PMSFCR_EL1_Type_FnE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_FnE r v)

def _set_PMSIDR_EL1_Type_Format (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_Format r v)

def _set_PMSIDR_EL1_Type_Interval (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_Interval r v)

def _set_PMSIDR_EL1_Type_LDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_LDS r v)

def _set_PMSIDR_EL1_Type_MaxSize (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_MaxSize r v)

def _set_PMSIDR_EL1_Type_PBT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_PBT r v)

def _set_PMSCR_EL1_Type_CX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL1_Type_CX r v)

def _set_HTRFCR_Type_CX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTRFCR_Type_CX r v)

def _set_PMSCR_EL2_Type_CX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL2_Type_CX r v)

def _set_TRFCR_EL2_Type_CX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_EL2_Type_CX r v)

def _set_PMSCR_EL1_Type_E0SPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL1_Type_E0SPE r v)

def _set_PMSCR_EL1_Type_E1SPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL1_Type_E1SPE r v)

def _set_PMSCR_EL1_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL1_Type_PA r v)

def _set_MFAR_EL3_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 56)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MFAR_EL3_Type_PA r v)

def _set_PAR_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 28)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_PA r v)

def _set_PFAR_EL1_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 56)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PFAR_EL1_Type_PA r v)

def _set_PFAR_EL2_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 56)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PFAR_EL2_Type_PA r v)

def _set_PMSCR_EL2_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL2_Type_PA r v)

def _set_PMSCR_EL1_Type_PCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL1_Type_PCT r v)

def _set_PMSCR_EL2_Type_PCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL2_Type_PCT r v)

def _set_PMSCR_EL2_Type_E0HSPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL2_Type_E0HSPE r v)

def _set_PMSCR_EL2_Type_E2SPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSCR_EL2_Type_E2SPE r v)

def _set_PMBLIMITR_EL1_Type_FM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBLIMITR_EL1_Type_FM r v)

def _set_PMBLIMITR_EL1_Type_LIMIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 52)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBLIMITR_EL1_Type_LIMIT r v)

def _set_PMBLIMITR_EL1_Type_PMFZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBLIMITR_EL1_Type_PMFZ r v)

def _set_PMBSR_EL1_Type_AssuredOnly (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBSR_EL1_Type_AssuredOnly r v)

def _set_PAR_EL1_Type_AssuredOnly (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_AssuredOnly r v)

def _set_VTCR_EL2_Type_AssuredOnly (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_AssuredOnly r v)

def _set_PMBSR_EL1_Type_COLL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBSR_EL1_Type_COLL r v)

def _set_PMBSR_EL1_Type_DL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBSR_EL1_Type_DL r v)

def _set_PMBSR_EL1_Type_DirtyBit (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBSR_EL1_Type_DirtyBit r v)

def _set_PAR_EL1_Type_DirtyBit (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_DirtyBit r v)

def _set_PMBSR_EL1_Type_MSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBSR_EL1_Type_MSS r v)

def _set_PMBSR_EL1_Type_Overlay (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBSR_EL1_Type_Overlay r v)

def _set_PAR_EL1_Type_Overlay (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_Overlay r v)

def _set_PMBSR_EL1_Type_S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBSR_EL1_Type_S r v)

def _set_DBGVCR32_EL2_Type_S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_S r v)

def _set_DBGVCR_Type_S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_S r v)

def _set_PAR_EL1_Type_S (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_S r v)

def _set_TTBR0_Type_S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_Type_S r v)

def _set_TTBR1_Type_S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_Type_S r v)

def _set_VTCR_Type_S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_S r v)

def _set_ZCR_EL1_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ZCR_EL1_Type_LEN r v)

def _set_SMCR_EL1_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL1_Type_LEN r v)

def _set_SMCR_EL2_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL2_Type_LEN r v)

def _set_SMCR_EL3_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL3_Type_LEN r v)

def _set_ZCR_EL2_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ZCR_EL2_Type_LEN r v)

def _set_ZCR_EL3_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ZCR_EL3_Type_LEN r v)

def _set_SMCR_EL1_Type_EZT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL1_Type_EZT0 r v)

def _set_SMCR_EL2_Type_EZT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL2_Type_EZT0 r v)

def _set_SMCR_EL3_Type_EZT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL3_Type_EZT0 r v)

def _set_SMCR_EL1_Type_FA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL1_Type_FA64 r v)

def _set_ID_AA64SMFR0_EL1_Type_FA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_FA64 r v)

def _set_SMCR_EL2_Type_FA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL2_Type_FA64 r v)

def _set_SMCR_EL3_Type_FA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMCR_EL3_Type_FA64 r v)

def _set_GCSPR_EL0_Type_PTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 61)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSPR_EL0_Type_PTR r v)

def _set_GCSPR_EL1_Type_PTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 61)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSPR_EL1_Type_PTR r v)

def _set_GCSPR_EL2_Type_PTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 61)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSPR_EL2_Type_PTR r v)

def _set_GCSPR_EL3_Type_PTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 61)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSPR_EL3_Type_PTR r v)

def _set_PMBPTR_EL1_Type_PTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBPTR_EL1_Type_PTR r v)

def _set_CPACR_EL1_Type_E0POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_EL1_Type_E0POE r v)

def _set_CPTR_EL2_Type_E0POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL2_Type_E0POE r v)

def _set_TCR2_EL1_Type_E0POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_E0POE r v)

def _set_TCR2_EL2_Type_E0POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_E0POE r v)

def _set_CPACR_EL1_Type_FPEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_EL1_Type_FPEN r v)

def _set_CPTR_EL2_Type_FPEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL2_Type_FPEN r v)

def _set_CPACR_EL1_Type_SMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_EL1_Type_SMEN r v)

def _set_CPTR_EL2_Type_SMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL2_Type_SMEN r v)

def _set_CPACR_EL1_Type_TTA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_EL1_Type_TTA r v)

def _set_CPTR_EL3_Type_TTA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL3_Type_TTA r v)

def _set_HCPTR_Type_TTA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCPTR_Type_TTA r v)

def _set_CPACR_EL1_Type_ZEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_EL1_Type_ZEN r v)

def _set_CPTR_EL2_Type_ZEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL2_Type_ZEN r v)

def _set_CPTR_EL2_Type_TAM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL2_Type_TAM r v)

def _set_CPTR_EL3_Type_TAM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL3_Type_TAM r v)

def _set_HCPTR_Type_TAM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCPTR_Type_TAM r v)

def _set_CPTR_EL2_Type_TCPAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL2_Type_TCPAC r v)

def _set_CPTR_EL3_Type_TCPAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL3_Type_TCPAC r v)

def _set_HCPTR_Type_TCPAC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCPTR_Type_TCPAC r v)

def _set_CPTR_EL2_Type_TFP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL2_Type_TFP r v)

def _set_CPTR_EL3_Type_TFP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL3_Type_TFP r v)

def _set_CPTR_EL2_Type_TSM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL2_Type_TSM r v)

def _set_CPTR_EL2_Type_TZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL2_Type_TZ r v)

def _set_CPTR_EL3_Type_ESM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL3_Type_ESM r v)

def _set_CPTR_EL3_Type_EZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPTR_EL3_Type_EZ r v)

def _set_CPACR_Type_ASEDIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_Type_ASEDIS r v)

def _set_CPACR_Type_TRCDIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_Type_TRCDIS r v)

def _set_CPACR_Type_cp10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_Type_cp10 r v)

def _set_NSACR_Type_cp10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NSACR_Type_cp10 r v)

def _set_CPACR_Type_cp11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CPACR_Type_cp11 r v)

def _set_NSACR_Type_cp11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NSACR_Type_cp11 r v)

def _set_HCPTR_Type_TASE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCPTR_Type_TASE r v)

def _set_HCPTR_Type_TCP10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCPTR_Type_TCP10 r v)

def _set_HCPTR_Type_TCP11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCPTR_Type_TCP11 r v)

def _set_NSACR_Type_NSASEDIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NSACR_Type_NSASEDIS r v)

def _set_NSACR_Type_NSTRCDIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NSACR_Type_NSTRCDIS r v)

def _set_DBGOSDLR_Type_DLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGOSDLR_Type_DLK r v)

def _set_EDPRSR_Type_DLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_DLK r v)

def _set_OSDLR_EL1_Type_DLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_OSDLR_EL1_Type_DLK r v)

def _set_DBGPRCR_EL1_Type_CORENPDRQ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGPRCR_EL1_Type_CORENPDRQ r v)

def _set_DBGPRCR_Type_CORENPDRQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGPRCR_Type_CORENPDRQ r v)

def _set_EDPRCR_Type_CORENPDRQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRCR_Type_CORENPDRQ r v)

def _set_GCSCR_EL1_Type_EXLOCKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL1_Type_EXLOCKEN r v)

def _set_GCSCR_EL2_Type_EXLOCKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL2_Type_EXLOCKEN r v)

def _set_GCSCR_EL3_Type_EXLOCKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL3_Type_EXLOCKEN r v)

def _set_GCSCR_EL1_Type_PCRSEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL1_Type_PCRSEL r v)

def _set_GCSCRE0_EL1_Type_PCRSEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_PCRSEL r v)

def _set_GCSCR_EL2_Type_PCRSEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL2_Type_PCRSEL r v)

def _set_GCSCR_EL3_Type_PCRSEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL3_Type_PCRSEL r v)

def _set_GCSCR_EL1_Type_PUSHMEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL1_Type_PUSHMEn r v)

def _set_GCSCRE0_EL1_Type_PUSHMEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_PUSHMEn r v)

def _set_GCSCR_EL2_Type_PUSHMEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL2_Type_PUSHMEn r v)

def _set_GCSCR_EL3_Type_PUSHMEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL3_Type_PUSHMEn r v)

def _set_GCSCR_EL1_Type_RVCHKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL1_Type_RVCHKEN r v)

def _set_GCSCRE0_EL1_Type_RVCHKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_RVCHKEN r v)

def _set_GCSCR_EL2_Type_RVCHKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL2_Type_RVCHKEN r v)

def _set_GCSCR_EL3_Type_RVCHKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL3_Type_RVCHKEN r v)

def _set_GCSCR_EL1_Type_STREn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL1_Type_STREn r v)

def _set_GCSCRE0_EL1_Type_STREn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_STREn r v)

def _set_GCSCR_EL2_Type_STREn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL2_Type_STREn r v)

def _set_GCSCR_EL3_Type_STREn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCR_EL3_Type_STREn r v)

/-- Type quantifiers: k_N : Nat, 4 < k_N -/
def IllegalExceptionReturn (spsr : (BitVec k_N)) : SailM Bool := SailME.run do
  let known ← (( do (undefined_bool ()) ) : SailME Bool Bool )
  let target ← (( do (undefined_bitvector 2) ) : SailME Bool (BitVec 2) )
  let target_el_is_aarch32 ← (( do (undefined_bool ()) ) : SailME Bool Bool )
  let valid_name ← (( do (undefined_bool ()) ) : SailME Bool Bool )
  let (target, valid_name) ← (( do
    let (tup__0, tup__1) ← do (ELFromSPSR spsr)
    let valid_name : Bool := tup__0
    let target : (BitVec 2) := tup__1
    (pure (target, valid_name)) ) : SailME Bool ((BitVec 2) × Bool) )
  if ((! valid_name) : Bool)
  then (pure true)
  else
    (do
      if (((BitVec.toNat target) >b (BitVec.toNat (← readReg PSTATE).EL)) : Bool)
      then (pure true)
      else
        (do
          let spsr_mode_is_aarch32 : Bool := ((BitVec.join1 [(BitVec.access spsr 4)]) == 1#1)
          let (known, target_el_is_aarch32) ← (( do
            let (tup__0, tup__1) ← do (ELUsingAArch32K target)
            let known : Bool := tup__0
            let target_el_is_aarch32 : Bool := tup__1
            (pure (known, target_el_is_aarch32)) ) : SailME Bool (Bool × Bool) )
          sail_assert (←((pure known) <||> (do
            (pure (target == EL0)) <&&> (do
              (pure (! (← (ELUsingAArch32 EL1)))))))) "src/v8_base.sail:8252.64-8252.65"
          if ((known && (neq_bool spsr_mode_is_aarch32 target_el_is_aarch32)) : Bool)
          then (pure true)
          else
            (do
              if (((← (UsingAArch32 ())) && (! spsr_mode_is_aarch32)) : Bool)
              then (pure true)
              else
                (do
                  if ((←((pure ((HaveEL EL2) && (target == EL1))) <&&> (do
                       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                  then
                    (do
                      if ((←((pure (! (← (IsSecureBelowEL3 ())))) <||> (do
                           (IsSecureEL2Enabled ())))) : Bool)
                      then SailME.throw (true : Bool)
                      else (pure ()))
                  else (pure ())
                  if ((←((HaveGCS ()) <&&> (do
                       (pure ((← readReg PSTATE).EXLOCK == 0#1))) <&&> (do
                       (pure ((← readReg PSTATE).EL == target))) <&&> (do
                       (GetCurrentEXLOCKEN ())) <&&> (do
                       (pure (! (← (Halted ()))))))) : Bool)
                  then (pure true)
                  else (pure false)))))

def _set_MDSCR_EL1_Type_EHBWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_EHBWE r v)

def _set_EDSCR2_Type_EHBWE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR2_Type_EHBWE r v)

def _set_MDSCR_EL1_Type_EMBWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_EMBWE r v)

def _set_MDSCR_EL1_Type_KDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_KDE r v)

def _set_MDSCR_EL1_Type_MDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDSCR_EL1_Type_MDE r v)

def _set_OSLSR_EL1_Type_OSLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_OSLSR_EL1_Type_OSLK r v)

def _set_DBGOSLSR_Type_OSLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGOSLSR_Type_OSLK r v)

def _set_EDPRSR_Type_OSLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_OSLK r v)

def _set_OSLAR_EL1_Type_OSLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_OSLAR_EL1_Type_OSLK r v)

def _set_OSLSR_EL1_Type_OSLM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_OSLSR_EL1_Type_OSLM r v)

def _set_DBGOSLSR_Type_OSLM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGOSLSR_Type_OSLM r v)

def _set_OSLSR_EL1_Type_nTT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_OSLSR_EL1_Type_nTT r v)

def _set_CTILSR_Type_nTT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTILSR_Type_nTT r v)

def _set_DBGOSLSR_Type_nTT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGOSLSR_Type_nTT r v)

def _set_EDLSR_Type_nTT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDLSR_Type_nTT r v)

def _set_PMLSR_Type_nTT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMLSR_Type_nTT r v)

def _set_HCR_Type_TAC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_TAC r v)

def _set_DBGBVR_EL1_Type_VA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 55)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_VA r v)

def _set_DBGBVR_Type_VA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 30)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBVR_Type_VA r v)

def _set_DBGWVR_EL1_Type_VA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 55)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWVR_EL1_Type_VA r v)

def _set_DBGWVR_Type_VA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 30)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWVR_Type_VA r v)

def _set_HSCTLR_Type_LSMAOE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_LSMAOE r v)

def _set_SCTLR_EL1_Type_LSMAOE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_LSMAOE r v)

def _set_SCTLR_EL2_Type_LSMAOE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_LSMAOE r v)

def _set_SCTLR_Type_LSMAOE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_LSMAOE r v)

def _set_HSCTLR_Type_nTLSMD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSCTLR_Type_nTLSMD r v)

def _set_SCTLR_EL1_Type_nTLSMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_nTLSMD r v)

def _set_SCTLR_EL2_Type_nTLSMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_nTLSMD r v)

def _set_SCTLR_Type_nTLSMD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_nTLSMD r v)

def _set_SCTLR_EL2_Type_ATA0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_ATA0 r v)

def _set_SCTLR_EL1_Type_ATA0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_ATA0 r v)

def _set_SCTLR_EL2_Type_BT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_BT r v)

def _set_DBGBCR_EL1_Type_BT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_BT r v)

def _set_DBGBCR_Type_BT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_Type_BT r v)

def _set_ID_AA64PFR1_EL1_Type_BT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_BT r v)

def _set_SCTLR_EL3_Type_BT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_BT r v)

def _set_SCTLR_EL2_Type_BT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_BT0 r v)

def _set_SCTLR_EL1_Type_BT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_BT0 r v)

def _set_SCTLR_EL2_Type_CMOW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_CMOW r v)

def _set_HCRX_EL2_Type_CMOW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_CMOW r v)

def _set_ID_AA64MMFR1_EL1_Type_CMOW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_CMOW r v)

def _set_SCTLR_EL1_Type_CMOW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_CMOW r v)

def _set_SCTLR_EL2_Type_EIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EIS r v)

def _set_SCTLR_EL1_Type_EIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EIS r v)

def _set_SCTLR_EL3_Type_EIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EIS r v)

def _set_SCTLR_EL2_Type_EOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EOS r v)

def _set_SCTLR_EL1_Type_EOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EOS r v)

def _set_SCTLR_EL3_Type_EOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EOS r v)

def _set_SCTLR_EL2_Type_EnALS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnALS r v)

def _set_HCRX_EL2_Type_EnALS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_EnALS r v)

def _set_SCTLR_EL1_Type_EnALS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnALS r v)

def _set_SCTLR_EL2_Type_EnASR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnASR r v)

def _set_HCRX_EL2_Type_EnASR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_EnASR r v)

def _set_SCTLR_EL1_Type_EnASR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnASR r v)

def _set_SCTLR_EL2_Type_EnDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnDA r v)

def _set_SCTLR_EL1_Type_EnDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnDA r v)

def _set_SCTLR_EL3_Type_EnDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EnDA r v)

def _set_SCTLR_EL2_Type_EnDB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnDB r v)

def _set_SCTLR_EL1_Type_EnDB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnDB r v)

def _set_SCTLR_EL3_Type_EnDB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EnDB r v)

def _set_SCTLR_EL2_Type_EnIA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnIA r v)

def _set_SCTLR_EL1_Type_EnIA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnIA r v)

def _set_SCTLR_EL3_Type_EnIA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EnIA r v)

def _set_SCTLR_EL2_Type_EnIB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnIB r v)

def _set_SCTLR_EL1_Type_EnIB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnIB r v)

def _set_SCTLR_EL3_Type_EnIB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EnIB r v)

def _set_SCTLR_EL2_Type_EnRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnRCTX r v)

def _set_SCTLR_EL1_Type_EnRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnRCTX r v)

def _set_SCTLR_Type_EnRCTX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_EnRCTX r v)

def _set_SCTLR_EL2_Type_ITFSB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_ITFSB r v)

def _set_SCTLR_EL1_Type_ITFSB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_ITFSB r v)

def _set_SCTLR_EL3_Type_ITFSB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_ITFSB r v)

def _set_SCTLR_EL2_Type_MSCEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_MSCEn r v)

def _set_HCRX_EL2_Type_MSCEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_MSCEn r v)

def _set_SCTLR_EL1_Type_MSCEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_MSCEn r v)

def _set_SCTLR_EL2_Type_TCF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TCF r v)

def _set_SCTLR_EL1_Type_TCF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TCF r v)

def _set_SCTLR_EL3_Type_TCF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_TCF r v)

def _set_SCTLR_EL2_Type_TCF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TCF0 r v)

def _set_SCTLR_EL1_Type_TCF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TCF0 r v)

def _set_SCTLR_EL2_Type_TCSO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TCSO r v)

def _set_SCTLR_EL1_Type_TCSO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TCSO r v)

def _set_SCTLR_EL3_Type_TCSO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL3_Type_TCSO r v)

def _set_SCTLR_EL2_Type_TCSO0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TCSO0 r v)

def _set_SCTLR_EL1_Type_TCSO0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TCSO0 r v)

def _set_SCTLR_EL1_Type_BT1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_EL1_Type_BT1 r v)

def _set_SCTLR_Type_AFE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_AFE r v)

def _set_SCTLR_Type_TRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_TRE r v)

def _set_SCTLR_Type_UNK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_UNK r v)

def _set_SCTLR_Type_UWXN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR_Type_UWXN r v)

/-- Type quantifiers: k_N : Nat, 26 < k_N -/
def RestoredITBits (spsr : (BitVec k_N)) : SailM (BitVec 8) := do
  let it : (BitVec 8) := ((Sail.BitVec.extractLsb spsr 15 10) +++ (Sail.BitVec.extractLsb spsr 26 25))
  if (((← readReg PSTATE).IL == 1#1) : Bool)
  then
    (do
      if ((← (ConstrainUnpredictableBool Unpredictable_ILZEROIT)) : Bool)
      then (pure 0b00000000#8)
      else (pure it))
  else
    (do
      if (((! (IsZero (Sail.BitVec.extractLsb it 7 4))) && (IsZero (Sail.BitVec.extractLsb it 3 0))) : Bool)
      then (pure 0b00000000#8)
      else
        (do
          let itd ← (( do
            if (((← readReg PSTATE).EL == EL2) : Bool)
            then (pure (_get_HSCTLR_Type_ITD (← (HSCTLR_read ()))))
            else (pure (_get_SCTLR_Type_ITD (← (SCTLR_read__2 ())))) ) : SailM (BitVec 1) )
          if (((((BitVec.join1 [(BitVec.access spsr 5)]) == 0#1) && (! (IsZero it))) || ((itd == 1#1) && (! (IsZero (Sail.BitVec.extractLsb it 2 0))))) : Bool)
          then (pure 0b00000000#8)
          else (pure it)))

def PLOfEL (el : (BitVec 2)) : SailM PrivilegeLevel := do
  let questionMark := el
  if ((questionMark == EL3) : Bool)
  then
    (do
      if ((! (← (HaveAArch64 ()))) : Bool)
      then (pure PL1)
      else (pure PL3))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then (pure PL2)
      else
        (do
          if ((questionMark == EL1) : Bool)
          then (pure PL1)
          else
            (do
              if ((questionMark == EL0) : Bool)
              then (pure PL0)
              else (do (undefined_PrivilegeLevel ())))))

def _set_ESR_EL1_Type_ISS2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL1_Type_ISS2 r v)

def _set_ESR_EL2_Type_ISS2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL2_Type_ISS2 r v)

def _set_ESR_EL3_Type_ISS2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ESR_EL3_Type_ISS2 r v)

def _set_HPFAR_EL2_Type_FIPA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 44)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HPFAR_EL2_Type_FIPA r v)

def _set_HPFAR_Type_FIPA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 28)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HPFAR_Type_FIPA r v)

def _set_MFAR_EL3_Type_FPA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 44)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MFAR_EL3_Type_FPA r v)

def _set_SPSR_abt_Type_J (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_abt_Type_J r v)

def _set_SPSR_fiq_Type_J (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_fiq_Type_J r v)

def _set_SPSR_hyp_Type_J (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_hyp_Type_J r v)

def _set_SPSR_irq_Type_J (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_irq_Type_J r v)

def _set_SPSR_mon_Type_J (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_mon_Type_J r v)

def _set_SPSR_svc_Type_J (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_svc_Type_J r v)

def _set_SPSR_und_Type_J (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPSR_und_Type_J r v)

def _set_EDECCR_Type_NSE0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_NSE0 r v)

def _set_EDECCR_Type_NSE1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_NSE1 r v)

def _set_EDECCR_Type_NSE2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_NSE2 r v)

def _set_EDECCR_Type_NSE3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_NSE3 r v)

def _set_EDECCR_Type_NSR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_NSR0 r v)

def _set_EDECCR_Type_NSR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_NSR1 r v)

def _set_EDECCR_Type_NSR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_NSR2 r v)

def _set_EDECCR_Type_NSR3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_NSR3 r v)

def _set_EDECCR_Type_RLE0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_RLE0 r v)

def _set_EDECCR_Type_RLE1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_RLE1 r v)

def _set_EDECCR_Type_RLE2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_RLE2 r v)

def _set_EDECCR_Type_RLR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_RLR0 r v)

def _set_EDECCR_Type_RLR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_RLR1 r v)

def _set_EDECCR_Type_RLR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_RLR2 r v)

def _set_EDECCR_Type_SE0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_SE0 r v)

def _set_EDECCR_Type_SE1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_SE1 r v)

def _set_EDECCR_Type_SE2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_SE2 r v)

def _set_EDECCR_Type_SE3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_SE3 r v)

def _set_EDECCR_Type_SR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_SR0 r v)

def _set_EDECCR_Type_SR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_SR1 r v)

def _set_EDECCR_Type_SR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_SR2 r v)

def _set_EDECCR_Type_SR3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDECCR_Type_SR3 r v)

def _set_OSECCR_EL1_Type_EDECCR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_OSECCR_EL1_Type_EDECCR r v)

def _set_DBGOSECCR_Type_EDECCR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGOSECCR_Type_EDECCR r v)

def _set_EDESR_Type_OSUC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDESR_Type_OSUC r v)

def _set_EDESR_Type_RC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDESR_Type_RC r v)

def BranchTargetCheck (_ : Unit) : SailM Unit := do
  sail_assert (←((HaveBTIExt ()) <&&> (do
    (pure (! (← (UsingAArch32 ()))))))) "src/v8_base.sail:10588.50-10588.51"
  if ((←(readReg InGuardedPage <&&> (do
       (pure ((← readReg PSTATE).BTYPE != 0b00#2))) <&&> (do
       (pure (! (← readReg BTypeCompatible)))) <&&> (do
       (pure (! (← (Halted ()))))))) : Bool)
  then
    (do
      let pc ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
      (AArch64_BranchTargetException (Sail.BitVec.extractLsb pc 51 0)))
  else (pure ())
  let branch_instr ← (( do (AArch64_ExecutingBROrBLROrRetInstr ()) ) : SailM Bool )
  let bti_instr ← (( do (AArch64_ExecutingBTIInstr ()) ) : SailM Bool )
  if ((! (branch_instr || bti_instr)) : Bool)
  then writeReg BTypeNext 0b00#2
  else (pure ())

def ConditionSyndrome (_ : Unit) : SailM (BitVec 5) := do
  let cond ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let syndrome ← (( do (undefined_bitvector 5) ) : SailM (BitVec 5) )
  if ((← (UsingAArch32 ())) : Bool)
  then
    (do
      let cond ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
      if (((← readReg PSTATE).T == 0#1) : Bool)
      then
        (do
          let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 1#1))
          if ((←((ConditionHolds cond) <&&> (do
               (ConstrainUnpredictableBool Unpredictable_ESRCONDPASS)))) : Bool)
          then (pure (Sail.BitVec.updateSubrange syndrome 3 0 0b1110#4))
          else (pure (Sail.BitVec.updateSubrange syndrome 3 0 cond)))
      else
        (do
          if ((← (__IMPDEF_boolean "Condition valid for trapped T32")) : Bool)
          then
            (let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 1#1))
            (pure (Sail.BitVec.updateSubrange syndrome 3 0 cond)))
          else
            (do
              let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 0#1))
              (pure (Sail.BitVec.updateSubrange syndrome 3 0 (← (__UNKNOWN_bits 4)))))))
  else
    (let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 1#1))
    (pure (Sail.BitVec.updateSubrange syndrome 3 0 0b1110#4)))

def WFETrapDelay (target_el : (BitVec 2)) : SailM (Bool × Int) := do
  let delay_enabled ← (( do (undefined_bool ()) ) : SailM Bool )
  let delay ← (( do (undefined_int ()) ) : SailM Int )
  let (delay, delay_enabled) ← (( do
    let questionMark := target_el
    let (delay, delay_enabled) ← (( do
      if ((questionMark == EL1) : Bool)
      then
        (do
          let (delay, delay_enabled) ← (( do
            if ((! (← (IsInHost ()))) : Bool)
            then
              (do
                let delay_enabled ← (pure ((_get_SCTLR_EL1_Type_TWEDEn (← readReg SCTLR_EL1)) == 1#1))
                let delay ← (pure (Int.shiftl 1 ((BitVec.toNat (_get_SCTLR_EL1_Type_TWEDEL (← readReg SCTLR_EL1))) +i 8)))
                (pure (delay, delay_enabled)))
            else
              (do
                let delay_enabled ← (pure ((_get_SCTLR_EL2_Type_TWEDEn (← readReg SCTLR_EL2)) == 1#1))
                let delay ← (pure (Int.shiftl 1 ((BitVec.toNat (_get_SCTLR_EL2_Type_TWEDEL (← readReg SCTLR_EL2))) +i 8)))
                (pure (delay, delay_enabled))) ) : SailM (Int × Bool) )
          (pure (delay, delay_enabled)))
      else
        (do
          let (delay, delay_enabled) ← (( do
            if ((questionMark == EL2) : Bool)
            then
              (do
                sail_assert (← (EL2Enabled ())) "src/v8_base.sail:10740.29-10740.30"
                let delay_enabled ← (pure ((_get_HCR_EL2_Type_TWEDEn (← readReg HCR_EL2)) == 1#1))
                let delay ← (pure (Int.shiftl 1 ((BitVec.toNat (_get_HCR_EL2_Type_TWEDEL (← readReg HCR_EL2))) +i 8)))
                (pure (delay, delay_enabled)))
            else
              (do
                let (delay, delay_enabled) ← (( do
                  if ((questionMark == EL3) : Bool)
                  then
                    (do
                      let delay_enabled ← (pure ((_get_SCR_EL3_Type_TWEDEn (← readReg SCR_EL3)) == 1#1))
                      let delay ← (pure (Int.shiftl 1 ((BitVec.toNat (_get_SCR_EL3_Type_TWEDEL (← readReg SCR_EL3))) +i 8)))
                      (pure (delay, delay_enabled)))
                  else (pure (delay, delay_enabled)) ) : SailM (Int × Bool) )
                (pure (delay, delay_enabled))) ) : SailM (Int × Bool) )
          (pure (delay, delay_enabled))) ) : SailM (Int × Bool) )
    (pure (delay, delay_enabled)) ) : SailM (Int × Bool) )
  let delay := delay
  (pure (delay_enabled, delay))

/-- Type quantifiers: localtimeout : Int -/
def WaitForEvent (localtimeout : Int) : SailM Unit := do
  if ((! (←((IsEventRegisterSet ()) <||> (do
         (HaveFeatWFxT ()) <&&> (do
           (LocalTimeoutEvent localtimeout)))))) : Bool)
  then
    (do
      writeReg IsWFEsleep true
      writeReg _DormantCtlReg (Sail.BitVec.updateSubrange (← readReg _DormantCtlReg) 10 10 1#1)
      (pure (EnterLowPowerState ())))
  else (pure ())

def InterruptPending (_ : Unit) : SailM Bool := do
  let fiq_pending ← (( do (undefined_bool ()) ) : SailM Bool )
  let irq_pending ← (( do (undefined_bool ()) ) : SailM Bool )
  let pending_virtual_interrupt : Bool := false
  let irq_pending ← (( do
    let (__tup_0, _) ← do (IRQPending ())
    (pure __tup_0) ) : SailM Bool )
  let fiq_pending : Bool :=
    let (__tup_0, _) := (FIQPending ())
    __tup_0
  let pending_physical_interrupt : Bool := ((irq_pending || fiq_pending) || (IsPhysicalSErrorPending ()))
  let pending_virtual_interrupt ← (( do
    if ((←((EL2Enabled ()) <&&> (do
         (pure ((← readReg PSTATE).EL == EL0)) <||> (do
           (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
         (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1))))) : Bool)
    then
      (do
        let virq_pending ← (( do (pure ((_get_HCR_EL2_Type_IMO (← readReg HCR_EL2)) == 1#1)) <&&> (do (VirtualIRQPending ()) <||> (do (pure ((_get_HCR_EL2_Type_VI (← readReg HCR_EL2)) == 1#1)))) ) : SailM Bool )
        let vfiq_pending ← (( do (pure ((_get_HCR_EL2_Type_FMO (← readReg HCR_EL2)) == 1#1)) <&&> (do (VirtualFIQPending ()) <||> (do (pure ((_get_HCR_EL2_Type_VF (← readReg HCR_EL2)) == 1#1)))) ) : SailM Bool )
        let vsei_pending ← (( do (pure ((_get_HCR_EL2_Type_AMO (← readReg HCR_EL2)) == 1#1)) <&&> (do (IsVirtualSErrorPending ()) <||> (do (pure ((_get_HCR_EL2_Type_VSE (← readReg HCR_EL2)) == 1#1)))) ) : SailM Bool )
        (pure ((vsei_pending || virq_pending) || vfiq_pending)))
    else (pure pending_virtual_interrupt) ) : SailM Bool )
  (pure (pending_physical_interrupt || pending_virtual_interrupt))

/-- Type quantifiers: localtimeout : Int -/
def WaitForInterrupt (localtimeout : Int) : SailM Unit := do
  if ((! (←((HaveFeatWFxT ()) <&&> (do
         (LocalTimeoutEvent localtimeout))))) : Bool)
  then
    (do
      writeReg IsWFIsleep true
      writeReg _DormantCtlReg (Sail.BitVec.updateSubrange (← readReg _DormantCtlReg) 0 0 1#1)
      (pure (EnterLowPowerState ())))
  else (pure ())

def _set_GCSCRE0_EL1_Type_nTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_nTR r v)

def _set_HCRX_EL2_Type_EnSDERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_EnSDERR r v)

def _set_HCRX_EL2_Type_EnSNERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_EnSNERR r v)

def _set_HCRX_EL2_Type_FGTnXS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_FGTnXS r v)

def _set_HCRX_EL2_Type_FnXS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_FnXS r v)

def _set_HCRX_EL2_Type_MCE2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_MCE2 r v)

def _set_HCRX_EL2_Type_SMPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_SMPME r v)

def _set_HCRX_EL2_Type_TALLINT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_TALLINT r v)

def _set_HCRX_EL2_Type_VFNMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_VFNMI r v)

def _set_HCRX_EL2_Type_VINMI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCRX_EL2_Type_VINMI r v)

def _set_MPAM2_EL2_Type_ALTSP_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_ALTSP_EL2 r v)

def _set_MPAM2_EL2_Type_ALTSP_FRCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_ALTSP_FRCD r v)

def _set_MPAM1_EL1_Type_ALTSP_FRCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM1_EL1_Type_ALTSP_FRCD r v)

def _set_MPAM2_EL2_Type_ALTSP_HFC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_ALTSP_HFC r v)

def _set_MPAM3_EL3_Type_ALTSP_HFC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_ALTSP_HFC r v)

def _set_MPAM2_EL2_Type_EnMPAMSM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_EnMPAMSM r v)

def _set_MPAM2_EL2_Type_MPAMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_MPAMEN r v)

def _set_MPAM1_EL1_Type_MPAMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM1_EL1_Type_MPAMEN r v)

def _set_MPAM3_EL3_Type_MPAMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_MPAMEN r v)

def _set_MPAM2_EL2_Type_PARTID_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_PARTID_D r v)

def _set_MPAM0_EL1_Type_PARTID_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM0_EL1_Type_PARTID_D r v)

def _set_MPAM1_EL1_Type_PARTID_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM1_EL1_Type_PARTID_D r v)

def _set_MPAM3_EL3_Type_PARTID_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_PARTID_D r v)

def _set_MPAMSM_EL1_Type_PARTID_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMSM_EL1_Type_PARTID_D r v)

def _set_MPAM2_EL2_Type_PARTID_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_PARTID_I r v)

def _set_MPAM0_EL1_Type_PARTID_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM0_EL1_Type_PARTID_I r v)

def _set_MPAM1_EL1_Type_PARTID_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM1_EL1_Type_PARTID_I r v)

def _set_MPAM3_EL3_Type_PARTID_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_PARTID_I r v)

def _set_MPAM2_EL2_Type_PMG_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_PMG_D r v)

def _set_MPAM0_EL1_Type_PMG_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM0_EL1_Type_PMG_D r v)

def _set_MPAM1_EL1_Type_PMG_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM1_EL1_Type_PMG_D r v)

def _set_MPAM3_EL3_Type_PMG_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_PMG_D r v)

def _set_MPAMSM_EL1_Type_PMG_D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMSM_EL1_Type_PMG_D r v)

def _set_MPAM2_EL2_Type_PMG_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_PMG_I r v)

def _set_MPAM0_EL1_Type_PMG_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM0_EL1_Type_PMG_I r v)

def _set_MPAM1_EL1_Type_PMG_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM1_EL1_Type_PMG_I r v)

def _set_MPAM3_EL3_Type_PMG_I (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_PMG_I r v)

def _set_MPAM2_EL2_Type_TIDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_TIDR r v)

def _set_MPAM2_EL2_Type_TRAPMPAM0EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_TRAPMPAM0EL1 r v)

def _set_MPAM2_EL2_Type_TRAPMPAM1EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM2_EL2_Type_TRAPMPAM1EL1 r v)

def _set_MPAM3_EL3_Type_ALTSP_EL3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_ALTSP_EL3 r v)

def _set_MPAM3_EL3_Type_ALTSP_HEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_ALTSP_HEN r v)

def _set_MPAM3_EL3_Type_FORCE_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_FORCE_NS r v)

def _set_MPAM3_EL3_Type_RT_ALTSP_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_RT_ALTSP_NS r v)

def _set_MPAM3_EL3_Type_SDEFLT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_SDEFLT r v)

def _set_MPAM3_EL3_Type_TRAPLOWER (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM3_EL3_Type_TRAPLOWER r v)

def _set_MPAM1_EL1_Type_FORCED_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAM1_EL1_Type_FORCED_NS r v)

def _set_MPAMIDR_EL1_Type_HAS_ALTSP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_HAS_ALTSP r v)

def _set_MPAMIDR_EL1_Type_HAS_FORCE_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_HAS_FORCE_NS r v)

def _set_MPAMIDR_EL1_Type_HAS_HCR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_HAS_HCR r v)

def _set_MPAMIDR_EL1_Type_HAS_SDEFLT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_HAS_SDEFLT r v)

def _set_MPAMIDR_EL1_Type_HAS_TIDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_HAS_TIDR r v)

def _set_MPAMIDR_EL1_Type_PARTID_MAX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_PARTID_MAX r v)

def _set_MPAMIDR_EL1_Type_PMG_MAX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_PMG_MAX r v)

def _set_MPAMIDR_EL1_Type_SP4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_SP4 r v)

def _set_MPAMIDR_EL1_Type_VPMR_MAX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_VPMR_MAX r v)

def _set_MPAMHCR_EL2_Type_EL0_VPMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMHCR_EL2_Type_EL0_VPMEN r v)

def _set_MPAMHCR_EL2_Type_EL1_VPMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMHCR_EL2_Type_EL1_VPMEN r v)

def _set_MPAMHCR_EL2_Type_GSTAPP_PLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMHCR_EL2_Type_GSTAPP_PLK r v)

def _set_MPAMHCR_EL2_Type_TRAP_MPAMIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMHCR_EL2_Type_TRAP_MPAMIDR_EL1 r v)

def _set_MPAMVPM0_EL2_Type_PhyPARTID0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM0_EL2_Type_PhyPARTID0 r v)

def _set_MPAMVPM0_EL2_Type_PhyPARTID1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM0_EL2_Type_PhyPARTID1 r v)

def _set_MPAMVPM0_EL2_Type_PhyPARTID2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM0_EL2_Type_PhyPARTID2 r v)

def _set_MPAMVPM0_EL2_Type_PhyPARTID3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM0_EL2_Type_PhyPARTID3 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V0 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V1 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V10 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V11 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V12 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V13 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V14 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V15 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V16 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V17 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V18 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V19 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V2 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V20 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V21 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V22 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V23 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V24 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V25 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V26 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V27 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V28 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V29 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V3 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V30 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V31 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V4 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V5 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V6 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V7 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V8 r v)

def _set_MPAMVPMV_EL2_Type_VPM_V9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V9 r v)

def _set_MPAMVPM1_EL2_Type_PhyPARTID4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM1_EL2_Type_PhyPARTID4 r v)

def _set_MPAMVPM1_EL2_Type_PhyPARTID5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM1_EL2_Type_PhyPARTID5 r v)

def _set_MPAMVPM1_EL2_Type_PhyPARTID6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM1_EL2_Type_PhyPARTID6 r v)

def _set_MPAMVPM1_EL2_Type_PhyPARTID7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM1_EL2_Type_PhyPARTID7 r v)

def _set_MPAMVPM2_EL2_Type_PhyPARTID10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM2_EL2_Type_PhyPARTID10 r v)

def _set_MPAMVPM2_EL2_Type_PhyPARTID11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM2_EL2_Type_PhyPARTID11 r v)

def _set_MPAMVPM2_EL2_Type_PhyPARTID8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM2_EL2_Type_PhyPARTID8 r v)

def _set_MPAMVPM2_EL2_Type_PhyPARTID9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM2_EL2_Type_PhyPARTID9 r v)

def _set_MPAMVPM3_EL2_Type_PhyPARTID12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM3_EL2_Type_PhyPARTID12 r v)

def _set_MPAMVPM3_EL2_Type_PhyPARTID13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM3_EL2_Type_PhyPARTID13 r v)

def _set_MPAMVPM3_EL2_Type_PhyPARTID14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM3_EL2_Type_PhyPARTID14 r v)

def _set_MPAMVPM3_EL2_Type_PhyPARTID15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM3_EL2_Type_PhyPARTID15 r v)

def _set_MPAMVPM4_EL2_Type_PhyPARTID16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM4_EL2_Type_PhyPARTID16 r v)

def _set_MPAMVPM4_EL2_Type_PhyPARTID17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM4_EL2_Type_PhyPARTID17 r v)

def _set_MPAMVPM4_EL2_Type_PhyPARTID18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM4_EL2_Type_PhyPARTID18 r v)

def _set_MPAMVPM4_EL2_Type_PhyPARTID19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM4_EL2_Type_PhyPARTID19 r v)

def _set_MPAMVPM5_EL2_Type_PhyPARTID20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM5_EL2_Type_PhyPARTID20 r v)

def _set_MPAMVPM5_EL2_Type_PhyPARTID21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM5_EL2_Type_PhyPARTID21 r v)

def _set_MPAMVPM5_EL2_Type_PhyPARTID22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM5_EL2_Type_PhyPARTID22 r v)

def _set_MPAMVPM5_EL2_Type_PhyPARTID23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM5_EL2_Type_PhyPARTID23 r v)

def _set_MPAMVPM6_EL2_Type_PhyPARTID24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM6_EL2_Type_PhyPARTID24 r v)

def _set_MPAMVPM6_EL2_Type_PhyPARTID25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM6_EL2_Type_PhyPARTID25 r v)

def _set_MPAMVPM6_EL2_Type_PhyPARTID26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM6_EL2_Type_PhyPARTID26 r v)

def _set_MPAMVPM6_EL2_Type_PhyPARTID27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM6_EL2_Type_PhyPARTID27 r v)

def _set_MPAMVPM7_EL2_Type_PhyPARTID28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM7_EL2_Type_PhyPARTID28 r v)

def _set_MPAMVPM7_EL2_Type_PhyPARTID29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM7_EL2_Type_PhyPARTID29 r v)

def _set_MPAMVPM7_EL2_Type_PhyPARTID30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM7_EL2_Type_PhyPARTID30 r v)

def _set_MPAMVPM7_EL2_Type_PhyPARTID31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPAMVPM7_EL2_Type_PhyPARTID31 r v)

/-- Type quantifiers: k_nontemporal : Bool, k_tagchecked : Bool -/
def CreateAccDescASIMD (memop : MemOp) (nontemporal : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_ASIMD) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc ← (pure { accdesc with streamingsve := ← (do (InStreamingMode ())) })
  let accdesc ← (( do
    if ((←((pure accdesc.streamingsve) <&&> (do
         (__IMPDEF_boolean "No tag checking of SIMD&FP loads and stores in Streaming SVE mode")))) : Bool)
    then (pure { accdesc with tagchecked := false })
    else (pure { accdesc with tagchecked := tagchecked }) ) : SailM AccessDescriptor )
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_tagchecked : Bool -/
def CreateAccDescASIMDAcqRel (memop : MemOp) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_ASIMD) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqpc := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with relsc := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc ← (pure { accdesc with streamingsve := ← (do (InStreamingMode ())) })
  let accdesc ← (( do
    if ((←((pure accdesc.streamingsve) <&&> (do
         (__IMPDEF_boolean "No tag checking of SIMD&FP loads and stores in Streaming SVE mode")))) : Bool)
    then (pure { accdesc with tagchecked := false })
    else (pure { accdesc with tagchecked := tagchecked }) ) : SailM AccessDescriptor )
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_contiguous : Bool, k_tagchecked : Bool -/
def CreateAccDescSVENF (contiguous : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_SVE) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with nonfault := true }
  let accdesc : AccessDescriptor := { accdesc with contiguous := contiguous }
  let accdesc ← (pure { accdesc with streamingsve := ← (do (InStreamingMode ())) })
  let accdesc ← (( do
    if ((←((pure accdesc.streamingsve) <&&> (do
         (__IMPDEF_boolean "No tag checking of SIMD&FP loads and stores in Streaming SVE mode")))) : Bool)
    then (pure { accdesc with tagchecked := false })
    else (pure { accdesc with tagchecked := tagchecked }) ) : SailM AccessDescriptor )
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_contiguous : Bool, k_tagchecked : Bool -/
def CreateAccDescSVEFF (contiguous : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_SVE) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with firstfault := true }
  let accdesc : AccessDescriptor := { accdesc with first := true }
  let accdesc : AccessDescriptor := { accdesc with contiguous := contiguous }
  let accdesc ← (pure { accdesc with streamingsve := ← (do (InStreamingMode ())) })
  let accdesc ← (( do
    if ((←((pure accdesc.streamingsve) <&&> (do
         (__IMPDEF_boolean "No tag checking of SIMD&FP loads and stores in Streaming SVE mode")))) : Bool)
    then (pure { accdesc with tagchecked := false })
    else (pure { accdesc with tagchecked := tagchecked }) ) : SailM AccessDescriptor )
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_contiguous : Bool, k_nontemporal : Bool, k_tagchecked : Bool -/
def CreateAccDescSVE (memop : MemOp) (nontemporal : Bool) (contiguous : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_SVE) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with contiguous := contiguous }
  let accdesc ← (pure { accdesc with streamingsve := ← (do (InStreamingMode ())) })
  let accdesc ← (( do
    if ((←((pure accdesc.streamingsve) <&&> (do
         (__IMPDEF_boolean "No tag checking of SIMD&FP loads and stores in Streaming SVE mode")))) : Bool)
    then (pure { accdesc with tagchecked := false })
    else (pure { accdesc with tagchecked := tagchecked }) ) : SailM AccessDescriptor )
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

def _set_CLIDR_EL1_Type_Ctype1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype1 r v)

def _set_CLIDR_Type_Ctype1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_Ctype1 r v)

def _set_CLIDR_EL1_Type_Ctype2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype2 r v)

def _set_CLIDR_Type_Ctype2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_Ctype2 r v)

def _set_CLIDR_EL1_Type_Ctype3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype3 r v)

def _set_CLIDR_Type_Ctype3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_Ctype3 r v)

def _set_CLIDR_EL1_Type_Ctype4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype4 r v)

def _set_CLIDR_Type_Ctype4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_Ctype4 r v)

def _set_CLIDR_EL1_Type_Ctype5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype5 r v)

def _set_CLIDR_Type_Ctype5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_Ctype5 r v)

def _set_CLIDR_EL1_Type_Ctype6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype6 r v)

def _set_CLIDR_Type_Ctype6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_Ctype6 r v)

def _set_CLIDR_EL1_Type_Ctype7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype7 r v)

def _set_CLIDR_Type_Ctype7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_Ctype7 r v)

def _set_CLIDR_EL1_Type_ICB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_ICB r v)

def _set_CLIDR_Type_ICB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_ICB r v)

def _set_CLIDR_EL1_Type_LoC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_LoC r v)

def _set_CLIDR_Type_LoC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_LoC r v)

def _set_CLIDR_EL1_Type_LoUIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_LoUIS r v)

def _set_CLIDR_Type_LoUIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_LoUIS r v)

def _set_CLIDR_EL1_Type_LoUU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_LoUU r v)

def _set_CLIDR_Type_LoUU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_Type_LoUU r v)

def _set_CLIDR_EL1_Type_Ttype1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype1 r v)

def _set_CLIDR_EL1_Type_Ttype2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype2 r v)

def _set_CLIDR_EL1_Type_Ttype3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype3 r v)

def _set_CLIDR_EL1_Type_Ttype4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype4 r v)

def _set_CLIDR_EL1_Type_Ttype5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype5 r v)

def _set_CLIDR_EL1_Type_Ttype6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype6 r v)

def _set_CLIDR_EL1_Type_Ttype7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype7 r v)

def DCInstNeedsTranslation (opscope : CacheOpScope) : SailM Bool := do
  if ((BEq.beq opscope CacheOpScope_PoE) : Bool)
  then (pure false)
  else
    (do
      if ((BEq.beq opscope CacheOpScope_PoPA) : Bool)
      then (pure false)
      else
        (do
          if (((_get_CLIDR_EL1_Type_LoC (← readReg CLIDR_EL1)) == 0b000#3) : Bool)
          then (pure (! (← (__IMPDEF_boolean "No fault generated for DC operations if PoC is before any level of cache"))))
          else
            (do
              if ((((_get_CLIDR_EL1_Type_LoUU (← readReg CLIDR_EL1)) == 0b000#3) && (BEq.beq opscope CacheOpScope_PoU)) : Bool)
              then (pure (! (← (__IMPDEF_boolean "No fault generated for DC operations if PoU is before any level of cache"))))
              else (pure true))))

def DecodeSW (regval : (BitVec 64)) (cachetype : CacheType) : SailM (Int × Int × Int) := do
  let linesize ← (( do (undefined_int ()) ) : SailM Int )
  let setnum ← (( do (undefined_int ()) ) : SailM Int )
  let waynum ← (( do (undefined_int ()) ) : SailM Int )
  let level := (BitVec.toNat (Sail.BitVec.extractLsb regval 3 1))
  let (setnum, waynum) ← (( do
    let (tup__0, tup__1, tup__2) ← do (GetCacheInfo level cachetype)
    let setnum : Int := tup__0
    let waynum : Int := tup__1
    let linesize : Int := tup__2
    (pure (setnum, waynum)) ) : SailM (Int × Int) )
  let waynum := waynum
  let setnum := setnum
  (pure (setnum, waynum, level))

def AESMixColumns (op : (BitVec 128)) : SailM (BitVec 128) := do
  let in0 : (BitVec 32) := ((((BitVec.slice op 96 8) +++ (BitVec.slice op 64 8)) +++ (BitVec.slice op 32 8)) +++ (BitVec.slice op 0 8))
  let in1 : (BitVec 32) := ((((BitVec.slice op 104 8) +++ (BitVec.slice op 72 8)) +++ (BitVec.slice op 40 8)) +++ (BitVec.slice op 8 8))
  let in2 : (BitVec 32) := ((((BitVec.slice op 112 8) +++ (BitVec.slice op 80 8)) +++ (BitVec.slice op 48 8)) +++ (BitVec.slice op 16 8))
  let in3 : (BitVec 32) := ((((BitVec.slice op 120 8) +++ (BitVec.slice op 88 8)) +++ (BitVec.slice op 56 8)) +++ (BitVec.slice op 24 8))
  let out0 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let out1 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let out2 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let out3 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (out0, out1, out2, out3) ← (( do
    let loop_c_lower := 0
    let loop_c_upper := 3
    let mut loop_vars := (out0, out1, out2, out3)
    for c in [loop_c_lower:loop_c_upper:1]i do
      let (out0, out1, out2, out3) := loop_vars
      loop_vars :=
        let out0 : (BitVec 32) := (set_slice 8 out0 (c *i 8) ((((FFmul02 (BitVec.slice in0 (c *i 8) 8)) ^^^ (FFmul03 (BitVec.slice in1 (c *i 8) 8))) ^^^ (BitVec.slice in2 (c *i 8) 8)) ^^^ (BitVec.slice in3 (c *i 8) 8)))
        let out1 : (BitVec 32) := (set_slice 8 out1 (c *i 8) ((((FFmul02 (BitVec.slice in1 (c *i 8) 8)) ^^^ (FFmul03 (BitVec.slice in2 (c *i 8) 8))) ^^^ (BitVec.slice in3 (c *i 8) 8)) ^^^ (BitVec.slice in0 (c *i 8) 8)))
        let out2 : (BitVec 32) := (set_slice 8 out2 (c *i 8) ((((FFmul02 (BitVec.slice in2 (c *i 8) 8)) ^^^ (FFmul03 (BitVec.slice in3 (c *i 8) 8))) ^^^ (BitVec.slice in0 (c *i 8) 8)) ^^^ (BitVec.slice in1 (c *i 8) 8)))
        let out3 : (BitVec 32) := (set_slice 8 out3 (c *i 8) ((((FFmul02 (BitVec.slice in3 (c *i 8) 8)) ^^^ (FFmul03 (BitVec.slice in0 (c *i 8) 8))) ^^^ (BitVec.slice in1 (c *i 8) 8)) ^^^ (BitVec.slice in2 (c *i 8) 8)))
        (out0, out1, out2, out3)
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32) × (BitVec 32)) )
  (pure ((((((((((((((((BitVec.slice out3 (3 *i 8) 8) +++ (BitVec.slice out2 (3 *i 8) 8)) +++ (BitVec.slice out1 (3 *i 8) 8)) +++ (BitVec.slice out0 (3 *i 8) 8)) +++ (BitVec.slice out3 (2 *i 8) 8)) +++ (BitVec.slice out2 (2 *i 8) 8)) +++ (BitVec.slice out1 (2 *i 8) 8)) +++ (BitVec.slice out0 (2 *i 8) 8)) +++ (BitVec.slice out3 (1 *i 8) 8)) +++ (BitVec.slice out2 (1 *i 8) 8)) +++ (BitVec.slice out1 (1 *i 8) 8)) +++ (BitVec.slice out0 (1 *i 8) 8)) +++ (BitVec.slice out3 (0 *i 8) 8)) +++ (BitVec.slice out2 (0 *i 8) 8)) +++ (BitVec.slice out1 (0 *i 8) 8)) +++ (BitVec.slice out0 (0 *i 8) 8)))

def AESInvMixColumns (op : (BitVec 128)) : SailM (BitVec 128) := do
  let in0 : (BitVec 32) := ((((BitVec.slice op 96 8) +++ (BitVec.slice op 64 8)) +++ (BitVec.slice op 32 8)) +++ (BitVec.slice op 0 8))
  let in1 : (BitVec 32) := ((((BitVec.slice op 104 8) +++ (BitVec.slice op 72 8)) +++ (BitVec.slice op 40 8)) +++ (BitVec.slice op 8 8))
  let in2 : (BitVec 32) := ((((BitVec.slice op 112 8) +++ (BitVec.slice op 80 8)) +++ (BitVec.slice op 48 8)) +++ (BitVec.slice op 16 8))
  let in3 : (BitVec 32) := ((((BitVec.slice op 120 8) +++ (BitVec.slice op 88 8)) +++ (BitVec.slice op 56 8)) +++ (BitVec.slice op 24 8))
  let out0 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let out1 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let out2 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let out3 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (out0, out1, out2, out3) ← (( do
    let loop_c_lower := 0
    let loop_c_upper := 3
    let mut loop_vars := (out0, out1, out2, out3)
    for c in [loop_c_lower:loop_c_upper:1]i do
      let (out0, out1, out2, out3) := loop_vars
      loop_vars :=
        let out0 : (BitVec 32) := (set_slice 8 out0 (c *i 8) ((((FFmul0E (BitVec.slice in0 (c *i 8) 8)) ^^^ (FFmul0B (BitVec.slice in1 (c *i 8) 8))) ^^^ (FFmul0D (BitVec.slice in2 (c *i 8) 8))) ^^^ (FFmul09 (BitVec.slice in3 (c *i 8) 8))))
        let out1 : (BitVec 32) := (set_slice 8 out1 (c *i 8) ((((FFmul09 (BitVec.slice in0 (c *i 8) 8)) ^^^ (FFmul0E (BitVec.slice in1 (c *i 8) 8))) ^^^ (FFmul0B (BitVec.slice in2 (c *i 8) 8))) ^^^ (FFmul0D (BitVec.slice in3 (c *i 8) 8))))
        let out2 : (BitVec 32) := (set_slice 8 out2 (c *i 8) ((((FFmul0D (BitVec.slice in0 (c *i 8) 8)) ^^^ (FFmul09 (BitVec.slice in1 (c *i 8) 8))) ^^^ (FFmul0E (BitVec.slice in2 (c *i 8) 8))) ^^^ (FFmul0B (BitVec.slice in3 (c *i 8) 8))))
        let out3 : (BitVec 32) := (set_slice 8 out3 (c *i 8) ((((FFmul0B (BitVec.slice in0 (c *i 8) 8)) ^^^ (FFmul0D (BitVec.slice in1 (c *i 8) 8))) ^^^ (FFmul09 (BitVec.slice in2 (c *i 8) 8))) ^^^ (FFmul0E (BitVec.slice in3 (c *i 8) 8))))
        (out0, out1, out2, out3)
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32) × (BitVec 32)) )
  (pure ((((((((((((((((BitVec.slice out3 (3 *i 8) 8) +++ (BitVec.slice out2 (3 *i 8) 8)) +++ (BitVec.slice out1 (3 *i 8) 8)) +++ (BitVec.slice out0 (3 *i 8) 8)) +++ (BitVec.slice out3 (2 *i 8) 8)) +++ (BitVec.slice out2 (2 *i 8) 8)) +++ (BitVec.slice out1 (2 *i 8) 8)) +++ (BitVec.slice out0 (2 *i 8) 8)) +++ (BitVec.slice out3 (1 *i 8) 8)) +++ (BitVec.slice out2 (1 *i 8) 8)) +++ (BitVec.slice out1 (1 *i 8) 8)) +++ (BitVec.slice out0 (1 *i 8) 8)) +++ (BitVec.slice out3 (0 *i 8) 8)) +++ (BitVec.slice out2 (0 *i 8) 8)) +++ (BitVec.slice out1 (0 *i 8) 8)) +++ (BitVec.slice out0 (0 *i 8) 8)))

/-- Type quantifiers: k_part1 : Bool -/
def SHA256hash (x_in : (BitVec 128)) (y_in : (BitVec 128)) (w : (BitVec 128)) (part1 : Bool) : SailM (BitVec 128) := do
  let chs ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let maj ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let t ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let x : (BitVec 128) := x_in
  let y : (BitVec 128) := y_in
  let (chs, maj, t, x, y) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := 3
    let mut loop_vars := (chs, maj, t, x, y)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (chs, maj, t, x, y) := loop_vars
      loop_vars ← do
        let chs : (BitVec 32) := (SHAchoose (Sail.BitVec.extractLsb y 31 0) (Sail.BitVec.extractLsb y 63 32) (Sail.BitVec.extractLsb y 95 64))
        let maj : (BitVec 32) := (SHAmajority (Sail.BitVec.extractLsb x 31 0) (Sail.BitVec.extractLsb x 63 32) (Sail.BitVec.extractLsb x 95 64))
        let t ← (pure ((((Sail.BitVec.extractLsb y 127 96) + (SHAhashSIGMA1 (Sail.BitVec.extractLsb y 31 0))) + chs) + (← (Elem_read w e 32))))
        let x : (BitVec 128) := (Sail.BitVec.updateSubrange x 127 96 (t + (Sail.BitVec.extractLsb x 127 96)))
        let y : (BitVec 128) := (Sail.BitVec.updateSubrange y 127 96 ((t + (SHAhashSIGMA0 (Sail.BitVec.extractLsb x 31 0))) + maj))
        let split_vec ← do (ROL (y +++ x) 32)
        let y : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 255 128)
        let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
        (pure (chs, maj, t, x, y))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32) × (BitVec 128) × (BitVec 128)) )
  if (part1 : Bool)
  then (pure x)
  else (pure y)

def _set_CONTEXTIDR_EL1_Type_PROCID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CONTEXTIDR_EL1_Type_PROCID r v)

def _set_CONTEXTIDR_EL2_Type_PROCID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CONTEXTIDR_EL2_Type_PROCID r v)

def _set_TTBCR_Type_EAE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_EAE r v)

def _set_TTBCR_Type_PD0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_PD0 r v)

def _set_TTBCR_Type_PD1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_PD1 r v)

def _set_TTBCR_Type_T2E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBCR_Type_T2E r v)

def _set_CONTEXTIDR_Type_ASID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CONTEXTIDR_Type_ASID r v)

def _set_TTBR0_EL1_Type_ASID (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL1_Type_ASID r v)

def _set_TTBR0_EL2_Type_ASID (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL2_Type_ASID r v)

def _set_TTBR0_Type_ASID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_Type_ASID r v)

def _set_TTBR1_EL1_Type_ASID (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_EL1_Type_ASID r v)

def _set_TTBR1_EL2_Type_ASID (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_EL2_Type_ASID r v)

def _set_TTBR1_Type_ASID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_Type_ASID r v)

def _set_TTBR0_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 47)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_Type_BADDR r v)

def _set_GPTBR_EL3_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 40)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPTBR_EL3_Type_BADDR r v)

def _set_HTTBR_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 47)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTTBR_Type_BADDR r v)

def _set_TTBR1_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 47)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_Type_BADDR r v)

def _set_VNCR_EL2_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 45)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VNCR_EL2_Type_BADDR r v)

def _set_VTTBR_Type_BADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 47)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTTBR_Type_BADDR r v)

def _set_TTBR0_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_Type_CnP r v)

def _set_HTTBR_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTTBR_Type_CnP r v)

def _set_ID_AA64MMFR2_EL1_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_CnP r v)

def _set_ID_MMFR4_EL1_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_CnP r v)

def _set_ID_MMFR4_Type_CnP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_Type_CnP r v)

def _set_TTBR0_EL1_Type_CnP (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL1_Type_CnP r v)

def _set_TTBR0_EL2_Type_CnP (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL2_Type_CnP r v)

def _set_TTBR0_EL3_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL3_Type_CnP r v)

def _set_TTBR1_EL1_Type_CnP (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_EL1_Type_CnP r v)

def _set_TTBR1_EL2_Type_CnP (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_EL2_Type_CnP r v)

def _set_TTBR1_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_Type_CnP r v)

def _set_VSTTBR_EL2_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSTTBR_EL2_Type_CnP r v)

def _set_VTTBR_EL2_Type_CnP (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTTBR_EL2_Type_CnP r v)

def _set_VTTBR_Type_CnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTTBR_Type_CnP r v)

def _set_TTBR0_Type_IRGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_Type_IRGN r v)

def _set_GPCCR_EL3_Type_IRGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPCCR_EL3_Type_IRGN r v)

def _set_TTBR1_Type_IRGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_Type_IRGN r v)

def _set_TTBR0_Type_NOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_Type_NOS r v)

def _set_PAR_Type_NOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_NOS r v)

def _set_TTBR1_Type_NOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_Type_NOS r v)

def _set_TTBR0_Type_RGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_Type_RGN r v)

def _set_TTBR1_Type_RGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_Type_RGN r v)

def _set_TTBR0_Type_TTB0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_Type_TTB0 r v)

def _set_TTBR0_EL1_Type_SKL (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL1_Type_SKL r v)

def _set_TTBR0_EL2_Type_SKL (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL2_Type_SKL r v)

def _set_TTBR0_EL3_Type_SKL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR0_EL3_Type_SKL r v)

def _set_TTBR1_EL1_Type_SKL (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_EL1_Type_SKL r v)

def _set_TTBR1_EL2_Type_SKL (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_EL2_Type_SKL r v)

def _set_VSTTBR_EL2_Type_SKL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSTTBR_EL2_Type_SKL r v)

def _set_VTTBR_EL2_Type_SKL (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTTBR_EL2_Type_SKL r v)

def _set_TTBR1_Type_TTB1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TTBR1_Type_TTB1 r v)

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def UnsignedRecipEstimate (operand : (BitVec k_N)) : SailM (BitVec k_N) := do
  let estimate ← (( do (undefined_int ()) ) : SailM Int )
  let increasedprecision_name ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert ((Sail.BitVec.length operand) == 32) "src/v8_base.sail:13084.19-13084.20"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length operand)) ) : SailM (BitVec k_N) )
  if (((BitVec.join1 [(BitVec.access operand ((Sail.BitVec.length result) -i 1))]) == 0#1) : Bool)
  then (pure (Ones (n := (Sail.BitVec.length result))))
  else
    (do
      let increasedprecision_name : Bool := false
      let estimate ← do (RecipEstimate (BitVec.toNat (Sail.BitVec.extractLsb operand 31 23)) increasedprecision_name)
      (pure ((integer_subrange estimate 8 0) +++ (Zeros (n := ((Sail.BitVec.length result) -i 9))))))

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def UnsignedRSqrtEstimate (operand : (BitVec k_N)) : SailM (BitVec k_N) := do
  let estimate ← (( do (undefined_int ()) ) : SailM Int )
  let increasedprecision_name ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert ((Sail.BitVec.length operand) == 32) "src/v8_base.sail:13158.19-13158.20"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length operand)) ) : SailM (BitVec k_N) )
  if (((Sail.BitVec.extractLsb operand ((Sail.BitVec.length result) -i 1) ((Sail.BitVec.length result) -i 2)) == 0b00#2) : Bool)
  then (pure (Ones (n := (Sail.BitVec.length result))))
  else
    (do
      let increasedprecision_name : Bool := false
      let estimate ← do (RecipSqrtEstimate (BitVec.toNat (Sail.BitVec.extractLsb operand 31 23)) increasedprecision_name)
      (pure ((integer_subrange estimate 8 0) +++ (Zeros (n := ((Sail.BitVec.length result) -i 9))))))

/-- Type quantifiers: N : Nat, i : Int, k_is_unsigned : Bool, N ≥ 0 -/
def SatQ (i : Int) (N : Nat) (is_unsigned : Bool) : SailM ((BitVec N) × Bool) := do
  let result ← (( do (undefined_bitvector N) ) : SailM (BitVec N) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (result, sat) ← (( do
    let (tup__0, tup__1) ← do
      if (is_unsigned : Bool)
      then
        (do
          sail_assert (0 ≤b (N -i 1)) "src/v8_base.sail:13218.38-13218.39"
          (UnsignedSatQ i N))
      else
        (do
          sail_assert (0 ≤b (N -i 1)) "src/v8_base.sail:13221.38-13221.39"
          (SignedSatQ i N))
    let result : (BitVec N) := tup__0
    let sat : Bool := tup__1
    (pure (result, sat)) ) : SailM ((BitVec N) × Bool) )
  (pure (result, sat))

def _set_MVBAR_Type_Reserved (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVBAR_Type_Reserved r v)

def _set_DFSR_Type_AET (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DFSR_Type_AET r v)

def _set_DISR_EL1_Type_AET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_EL1_Type_AET r v)

def _set_VDFSR_Type_AET (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDFSR_Type_AET r v)

def _set_VDISR_EL2_Type_AET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_EL2_Type_AET r v)

def _set_VDISR_Type_AET (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_Type_AET r v)

def _set_VSESR_EL2_Type_AET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSESR_EL2_Type_AET r v)

def _set_DFSR_Type_CM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DFSR_Type_CM r v)

def _set_EDHSR_Type_CM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDHSR_Type_CM r v)

def _set_DFSR_Type_Domain (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DFSR_Type_Domain r v)

def _set_DFSR_Type_ExT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DFSR_Type_ExT r v)

def _set_DISR_Type_ExT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_Type_ExT r v)

def _set_IFSR32_EL2_Type_ExT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR32_EL2_Type_ExT r v)

def _set_IFSR_Type_ExT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR_Type_ExT r v)

def _set_VDFSR_Type_ExT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDFSR_Type_ExT r v)

def _set_VDISR_EL2_Type_ExT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_EL2_Type_ExT r v)

def _set_VDISR_Type_ExT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_Type_ExT r v)

def _set_VSESR_EL2_Type_ExT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSESR_EL2_Type_ExT r v)

def _set_DFSR_Type_FS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DFSR_Type_FS r v)

def _set_DISR_Type_FS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_Type_FS r v)

def _set_IFSR32_EL2_Type_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR32_EL2_Type_FS r v)

def _set_IFSR_Type_FS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR_Type_FS r v)

def _set_ISR_EL1_Type_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ISR_EL1_Type_FS r v)

def _set_PAR_Type_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_FS r v)

def _set_VDISR_EL2_Type_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_EL2_Type_FS r v)

def _set_VDISR_Type_FS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_Type_FS r v)

def _set_DFSR_Type_FnV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DFSR_Type_FnV r v)

def _set_EDHSR_Type_FnV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDHSR_Type_FnV r v)

def _set_IFSR32_EL2_Type_FnV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR32_EL2_Type_FnV r v)

def _set_IFSR_Type_FnV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR_Type_FnV r v)

def _set_DFSR_Type_LPAE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DFSR_Type_LPAE r v)

def _set_DISR_Type_LPAE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_Type_LPAE r v)

def _set_IFSR32_EL2_Type_LPAE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR32_EL2_Type_LPAE r v)

def _set_IFSR_Type_LPAE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_IFSR_Type_LPAE r v)

def _set_PAR_Type_LPAE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_LPAE r v)

def _set_VDISR_EL2_Type_LPAE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_EL2_Type_LPAE r v)

def _set_VDISR_Type_LPAE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_Type_LPAE r v)

def _set_DFSR_Type_WnR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DFSR_Type_WnR r v)

def _set_EDHSR_Type_WnR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDHSR_Type_WnR r v)

def _set_DBGDSCRext_Type_MDBGen (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_MDBGen r v)

def _set_DBGDSCRint_Type_MDBGen (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRint_Type_MDBGen r v)

def _set_DBGDSCRint_Type_MOE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRint_Type_MOE r v)

def _set_DBGDSCRext_Type_SPIDdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_SPIDdis r v)

def _set_DBGDSCRint_Type_SPIDdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRint_Type_SPIDdis r v)

def _set_DBGDSCRext_Type_SPNIDdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_SPNIDdis r v)

def _set_DBGDSCRint_Type_SPNIDdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRint_Type_SPNIDdis r v)

def _set_DBGDSCRext_Type_UDCCdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_UDCCdis r v)

def _set_DBGDSCRint_Type_UDCCdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRint_Type_UDCCdis r v)

def _set_SCTLR2_EL1_Type_EnADERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL1_Type_EnADERR r v)

def _set_SCTLR2_EL2_Type_EnADERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_EnADERR r v)

def _set_SCTLR2_EL3_Type_EnADERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL3_Type_EnADERR r v)

def _set_SCTLR2_EL1_Type_EnANERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL1_Type_EnANERR r v)

def _set_SCTLR2_EL2_Type_EnANERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_EnANERR r v)

def _set_SCTLR2_EL3_Type_EnANERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL3_Type_EnANERR r v)

def _set_SCTLR2_EL2_Type_EMEC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_EMEC r v)

def _set_SCTLR2_EL3_Type_EMEC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SCTLR2_EL3_Type_EMEC r v)

def _set_FPEXC32_EL2_Type_DEX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_DEX r v)

def _set_FPEXC_Type_DEX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_DEX r v)

def _set_FPEXC32_EL2_Type_DZF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_DZF r v)

def _set_FPEXC_Type_DZF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_DZF r v)

def _set_FPEXC32_EL2_Type_EN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_EN r v)

def _set_AMUSERENR_EL0_Type_EN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMUSERENR_EL0_Type_EN r v)

def _set_AMUSERENR_Type_EN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMUSERENR_Type_EN r v)

def _set_CNTCR_Type_EN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTCR_Type_EN r v)

def _set_FPEXC_Type_EN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_EN r v)

def _set_LORC_EL1_Type_EN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORC_EL1_Type_EN r v)

def _set_PMPCSCTL_Type_EN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPCSCTL_Type_EN r v)

def _set_PMUSERENR_EL0_Type_EN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_EN r v)

def _set_PMUSERENR_Type_EN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_Type_EN r v)

def _set_FPEXC32_EL2_Type_EX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_EX r v)

def _set_FPEXC_Type_EX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_EX r v)

def _set_PMCFGR_Type_EX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_EX r v)

def _set_FPEXC32_EL2_Type_FP2V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_FP2V r v)

def _set_FPEXC_Type_FP2V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_FP2V r v)

def _set_FPEXC32_EL2_Type_IDF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_IDF r v)

def _set_FPEXC_Type_IDF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_IDF r v)

def _set_FPEXC32_EL2_Type_IOF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_IOF r v)

def _set_FPEXC_Type_IOF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_IOF r v)

def _set_FPEXC32_EL2_Type_IXF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_IXF r v)

def _set_FPEXC_Type_IXF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_IXF r v)

def _set_FPEXC32_EL2_Type_OFF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_OFF r v)

def _set_FPEXC_Type_OFF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_OFF r v)

def _set_FPEXC32_EL2_Type_TFV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_TFV r v)

def _set_FPEXC_Type_TFV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_TFV r v)

def _set_FPEXC32_EL2_Type_UFF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_UFF r v)

def _set_FPEXC_Type_UFF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_UFF r v)

def _set_FPEXC32_EL2_Type_VECITR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_VECITR r v)

def _set_FPEXC_Type_VECITR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_VECITR r v)

def _set_FPEXC32_EL2_Type_VV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_VV r v)

def _set_FPEXC_Type_VV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPEXC_Type_VV r v)

def AArch32_FPTrappedException (accumulated_exceptions : (BitVec 8)) : SailM Unit := do
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let is_ase ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((← (AArch32_GeneralExceptionsToAArch64 ())) : Bool)
  then
    (do
      let is_ase : Bool := false
      let element : Int := 0
      (AArch64_FPTrappedException is_ase accumulated_exceptions))
  else (pure ())
  (FPEXC_write (_update_FPEXC_Type_DEX (← (FPEXC_read ())) 1#1))
  (FPEXC_write (_update_FPEXC_Type_TFV (← (FPEXC_read ())) 1#1))
  (FPEXC_write (Mk_FPEXC_Type (Sail.BitVec.updateSubrange (← (FPEXC_read ())) 7 7 (BitVec.slice ((BitVec.join1 [(BitVec.access accumulated_exceptions 7)]) +++ (Sail.BitVec.extractLsb accumulated_exceptions 4 0)) 5 1))))
  (FPEXC_write (Mk_FPEXC_Type (Sail.BitVec.updateSubrange (← (FPEXC_read ())) 4 0 (BitVec.slice ((BitVec.join1 [(BitVec.access accumulated_exceptions 7)]) +++ (Sail.BitVec.extractLsb accumulated_exceptions 4 0)) 0 5))))
  (FPEXC_write (Mk_FPEXC_Type (Sail.BitVec.updateSubrange (← (FPEXC_read ())) 10 8 0b111#3)))
  (AArch32_TakeUndefInstrException ())

def IsFullA64Enabled (_ : Unit) : SailM Bool := SailME.run do
  if ((! (← (HaveSMEFullA64 ()))) : Bool)
  then (pure false)
  else
    (do
      if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
           (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
           (pure (! (← (IsInHost ()))))))) : Bool)
      then
        (do
          if (((_get_SMCR_EL1_Type_FA64 (← readReg SMCR_EL1)) == 0#1) : Bool)
          then SailME.throw (false : Bool)
          else (pure ()))
      else (pure ())
      if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
           (pure ((← readReg PSTATE).EL == EL1)) <||> (do
             (pure ((← readReg PSTATE).EL == EL2)))) <&&> (do
           (EL2Enabled ())))) : Bool)
      then
        (do
          if (((_get_SMCR_EL2_Type_FA64 (← readReg SMCR_EL2)) == 0#1) : Bool)
          then SailME.throw (false : Bool)
          else (pure ()))
      else (pure ())
      if ((HaveEL EL3) : Bool)
      then
        (do
          if (((_get_SMCR_EL3_Type_FA64 (← readReg SMCR_EL3)) == 0#1) : Bool)
          then SailME.throw (false : Bool)
          else (pure ()))
      else (pure ())
      (pure true))

def FPDecodeRounding (rmode : (BitVec 2)) : SailM FPRounding := do
  match (rmode : BitVec 2) with
  | 0b00 => (pure FPRounding_TIEEVEN)
  | 0b01 => (pure FPRounding_POSINF)
  | 0b10 => (pure FPRounding_NEGINF)
  | 0b11 => (pure FPRounding_ZERO)
  | _ => (do (undefined_FPRounding ()))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPDefaultNaN__1 (fpcr : (BitVec 64)) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:16128.38-16128.39"
  let E :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F := (N -i (E +i 1))
  let sign ← (( do
    if ((←((HaveAltFP ()) <&&> (do
         (pure (! (← (UsingAArch32 ()))))))) : Bool)
    then (pure (_get_FPCRType_AH fpcr))
    else (pure 0#1) ) : SailM (BitVec 1) )
  let exp : (BitVec E) := (Ones (n := E))
  let frac : (BitVec F) := (1#1 +++ (Zeros (n := (F -i 1))))
  (pure ((sign +++ exp) +++ frac))

def FPDecodeRM (rm : (BitVec 2)) : SailM FPRounding := do
  let result ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  match (rm : BitVec 2) with
  | 0b00 => (pure FPRounding_TIEAWAY)
  | 0b01 => (pure FPRounding_TIEEVEN)
  | 0b10 => (pure FPRounding_POSINF)
  | _ => (pure FPRounding_NEGINF)

def _set_CNTHP_CTL_EL2_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CTL_EL2_Type_ENABLE r v)

def _set_CNTHPS_CTL_EL2_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_CTL_EL2_Type_ENABLE r v)

def _set_CNTHPS_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_CTL_Type_ENABLE r v)

def _set_CNTHP_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CTL_Type_ENABLE r v)

def _set_CNTHVS_CTL_EL2_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_CTL_EL2_Type_ENABLE r v)

def _set_CNTHVS_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_CTL_Type_ENABLE r v)

def _set_CNTHV_CTL_EL2_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_CTL_EL2_Type_ENABLE r v)

def _set_CNTHV_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_CTL_Type_ENABLE r v)

def _set_CNTPS_CTL_EL1_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTPS_CTL_EL1_Type_ENABLE r v)

def _set_CNTP_CTL_EL0_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CTL_EL0_Type_ENABLE r v)

def _set_CNTP_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CTL_Type_ENABLE r v)

def _set_CNTV_CTL_EL0_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CTL_EL0_Type_ENABLE r v)

def _set_CNTV_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CTL_Type_ENABLE r v)

def _set_CNTHP_CTL_EL2_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CTL_EL2_Type_IMASK r v)

def _set_CNTHPS_CTL_EL2_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_CTL_EL2_Type_IMASK r v)

def _set_CNTHPS_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_CTL_Type_IMASK r v)

def _set_CNTHP_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CTL_Type_IMASK r v)

def _set_CNTHVS_CTL_EL2_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_CTL_EL2_Type_IMASK r v)

def _set_CNTHVS_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_CTL_Type_IMASK r v)

def _set_CNTHV_CTL_EL2_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_CTL_EL2_Type_IMASK r v)

def _set_CNTHV_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_CTL_Type_IMASK r v)

def _set_CNTPS_CTL_EL1_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTPS_CTL_EL1_Type_IMASK r v)

def _set_CNTP_CTL_EL0_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CTL_EL0_Type_IMASK r v)

def _set_CNTP_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CTL_Type_IMASK r v)

def _set_CNTV_CTL_EL0_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CTL_EL0_Type_IMASK r v)

def _set_CNTV_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CTL_Type_IMASK r v)

def _set_CNTHP_CTL_EL2_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CTL_EL2_Type_ISTATUS r v)

def _set_CNTHPS_CTL_EL2_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_CTL_EL2_Type_ISTATUS r v)

def _set_CNTHPS_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_CTL_Type_ISTATUS r v)

def _set_CNTHVS_CTL_EL2_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_CTL_EL2_Type_ISTATUS r v)

def _set_CNTHVS_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_CTL_Type_ISTATUS r v)

def _set_CNTHV_CTL_EL2_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_CTL_EL2_Type_ISTATUS r v)

def _set_CNTHV_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_CTL_Type_ISTATUS r v)

def _set_CNTPS_CTL_EL1_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTPS_CTL_EL1_Type_ISTATUS r v)

def _set_CNTP_CTL_EL0_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CTL_EL0_Type_ISTATUS r v)

def _set_CNTV_CTL_EL0_Type_ISTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CTL_EL0_Type_ISTATUS r v)

def _set_CNTV_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CTL_Type_ISTATUS r v)

def _set_CNTHP_CVAL_EL2_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CVAL_EL2_Type_CompareValue r v)

def _set_CNTHPS_CVAL_EL2_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_CVAL_EL2_Type_CompareValue r v)

def _set_CNTHP_CVAL_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CVAL_Type_CompareValue r v)

def _set_CNTHVS_CVAL_EL2_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_CVAL_EL2_Type_CompareValue r v)

def _set_CNTHV_CVAL_EL2_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_CVAL_EL2_Type_CompareValue r v)

def _set_CNTPS_CVAL_EL1_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTPS_CVAL_EL1_Type_CompareValue r v)

def _set_CNTP_CVAL_EL0_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CVAL_EL0_Type_CompareValue r v)

def _set_CNTP_CVAL_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CVAL_Type_CompareValue r v)

def _set_CNTV_CVAL_EL0_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CVAL_EL0_Type_CompareValue r v)

def _set_CNTV_CVAL_Type_CompareValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_CVAL_Type_CompareValue r v)

def _set_CNTCR_Type_FCREQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 10)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTCR_Type_FCREQ r v)

def _set_CNTCR_Type_HDBG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTCR_Type_HDBG r v)

def _set_AMCFGR_EL0_Type_HDBG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCFGR_EL0_Type_HDBG r v)

def _set_AMCFGR_Type_HDBG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCFGR_Type_HDBG r v)

def _set_AMCR_EL0_Type_HDBG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCR_EL0_Type_HDBG r v)

def _set_AMCR_Type_HDBG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCR_Type_HDBG r v)

def _set_CNTCR_Type_SCEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTCR_Type_SCEN r v)

def _set_CNTSCR_Type_ScaleVal (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTSCR_Type_ScaleVal r v)

def _set_GPCCR_EL3_Type_GPC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPCCR_EL3_Type_GPC r v)

def _set_GPCCR_EL3_Type_GPCP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPCCR_EL3_Type_GPCP r v)

def _set_GPCCR_EL3_Type_L0GPTSZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPCCR_EL3_Type_L0GPTSZ r v)

def _set_GPCCR_EL3_Type_ORGN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPCCR_EL3_Type_ORGN r v)

def _set_GPCCR_EL3_Type_PGS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPCCR_EL3_Type_PGS r v)

def _set_GPCCR_EL3_Type_PPS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GPCCR_EL3_Type_PPS r v)

def _set_TCR2_EL1_Type_DisCH1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL1_Type_DisCH1 r v)

def _set_TCR2_EL2_Type_DisCH1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_DisCH1 r v)

def _set_TCR2_EL2_Type_AMEC0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_AMEC0 r v)

def _set_TCR2_EL2_Type_AMEC1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_AMEC1 r v)

def _set_TCR2_EL2_Type_SKL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_SKL0 r v)

def _set_TCR2_EL2_Type_SKL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TCR2_EL2_Type_SKL1 r v)

/-- Type quantifiers: k_data : Bool -/
def AddPAC (ptr : (BitVec 64)) (modifier : (BitVec 64)) (K : (BitVec 128)) (data : Bool) : SailM (BitVec 64) := do
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let ext_ptr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let selbit ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let isgeneric : Bool := false
  let tbi ← (( do (pure ((← (EffectiveTBI ptr (! data) (← readReg PSTATE).EL)) == 1#1)) ) : SailM Bool )
  let mtx ← (( do (pure ((← (EffectiveMTX ptr (! data) (← readReg PSTATE).EL)) == 1#1)) ) : SailM Bool )
  let top_bit :=
    if (tbi : Bool)
    then 55
    else 63
  let selbit ← (( do
    if ((← (PtrHasUpperAndLowerAddRanges ())) : Bool)
    then
      (do
        sail_assert (←((pure ((← (S1TranslationRegime__1 ())) == EL1)) <||> (do
          (pure ((← (S1TranslationRegime__1 ())) == EL2))))) "src/v8_base.sail:21714.80-21714.81"
        if (((← (S1TranslationRegime__1 ())) == EL1) : Bool)
        then
          (do
            if (data : Bool)
            then
              (do
                if ((←((pure ((_get_TCR_EL1_Type_TBI1 (← readReg TCR_EL1)) == 1#1)) <||> (do
                     (pure ((_get_TCR_EL1_Type_TBI0 (← readReg TCR_EL1)) == 1#1))))) : Bool)
                then (pure (BitVec.join1 [(BitVec.access ptr 55)]))
                else (pure (BitVec.join1 [(BitVec.access ptr 63)])))
            else
              (do
                if ((←((pure ((_get_TCR_EL1_Type_TBI1 (← readReg TCR_EL1)) == 1#1)) <&&> (do
                     (pure ((_get_TCR_EL1_Type_TBID1 (← readReg TCR_EL1)) == 0#1))) <||> (do
                     (pure ((_get_TCR_EL1_Type_TBI0 (← readReg TCR_EL1)) == 1#1)) <&&> (do
                       (pure ((_get_TCR_EL1_Type_TBID0 (← readReg TCR_EL1)) == 0#1)))))) : Bool)
                then (pure (BitVec.join1 [(BitVec.access ptr 55)]))
                else (pure (BitVec.join1 [(BitVec.access ptr 63)]))))
        else
          (do
            if (data : Bool)
            then
              (do
                if ((←((pure ((_get_TCR_EL2_Type_TBI1 (← readReg TCR_EL2)) == 1#1)) <||> (do
                     (pure ((_get_TCR_EL2_Type_TBI0 (← readReg TCR_EL2)) == 1#1))))) : Bool)
                then (pure (BitVec.join1 [(BitVec.access ptr 55)]))
                else (pure (BitVec.join1 [(BitVec.access ptr 63)])))
            else
              (do
                if ((←((pure ((_get_TCR_EL2_Type_TBI1 (← readReg TCR_EL2)) == 1#1)) <&&> (do
                     (pure ((_get_TCR_EL2_Type_TBID1 (← readReg TCR_EL2)) == 0#1))) <||> (do
                     (pure ((_get_TCR_EL2_Type_TBI0 (← readReg TCR_EL2)) == 1#1)) <&&> (do
                       (pure ((_get_TCR_EL2_Type_TBID0 (← readReg TCR_EL2)) == 0#1)))))) : Bool)
                then (pure (BitVec.join1 [(BitVec.access ptr 55)]))
                else (pure (BitVec.join1 [(BitVec.access ptr 63)])))))
    else
      (if (tbi : Bool)
      then (pure (BitVec.join1 [(BitVec.access ptr 55)]))
      else (pure (BitVec.join1 [(BitVec.access ptr 63)]))) ) : SailM (BitVec 1) )
  let selbit ← (( do
    if ((←((HaveEnhancedPAC2 ()) <&&> (do
         (ConstPACField ())))) : Bool)
    then (pure (BitVec.join1 [(BitVec.access ptr 55)]))
    else (pure selbit) ) : SailM (BitVec 1) )
  let selbit := selbit
  let bottom_PAC_bit ← do (CalculateBottomPACBit selbit)
  if ((tbi && (bottom_PAC_bit ≥b 55)) : Bool)
  then (pure ptr)
  else
    (do
      let extfield : (BitVec 64) := (BitVec.replicateBits selbit 64)
      let ext_ptr ← (( do
        if (tbi : Bool)
        then
          (do
            sail_assert ((0 ≤b ((56 -i bottom_PAC_bit) -i 1)) && (((56 -i bottom_PAC_bit) -i 1) <b 64)) "src/v8_base.sail:21757.90-21757.91"
            sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21758.80-21758.81"
            (pure (((Sail.BitVec.extractLsb ptr 63 56) +++ (Sail.BitVec.extractLsb extfield ((56 -i bottom_PAC_bit) -i 1) 0)) +++ (Sail.BitVec.extractLsb ptr (bottom_PAC_bit -i 1) 0))))
        else
          (do
            if (mtx : Bool)
            then
              (do
                sail_assert ((0 ≤b ((56 -i bottom_PAC_bit) -i 1)) && (((56 -i bottom_PAC_bit) -i 1) <b 64)) "src/v8_base.sail:21761.90-21761.91"
                sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21762.80-21762.81"
                (pure ((((Sail.BitVec.extractLsb extfield 63 60) +++ (Sail.BitVec.extractLsb ptr 59 56)) +++ (Sail.BitVec.extractLsb extfield ((56 -i bottom_PAC_bit) -i 1) 0)) +++ (Sail.BitVec.extractLsb ptr (bottom_PAC_bit -i 1) 0))))
            else
              (do
                sail_assert ((0 ≤b ((64 -i bottom_PAC_bit) -i 1)) && (((64 -i bottom_PAC_bit) -i 1) <b 64)) "src/v8_base.sail:21765.90-21765.91"
                sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21766.80-21766.81"
                (pure ((Sail.BitVec.extractLsb extfield ((64 -i bottom_PAC_bit) -i 1) 0) +++ (Sail.BitVec.extractLsb ptr (bottom_PAC_bit -i 1) 0))))) ) : SailM (BitVec 64) )
      let PAC ← (( do (ComputePAC ext_ptr modifier (Sail.BitVec.extractLsb K 127 64) (Sail.BitVec.extractLsb K 63 0) isgeneric) ) : SailM (BitVec 64) )
      let unusedbits_mask : (BitVec 64) := (Zeros (n := 64))
      sail_assert ((0 ≤b bottom_PAC_bit) && (bottom_PAC_bit ≤b 54)) "src/v8_base.sail:21771.69-21771.70"
      let unusedbits_mask : (BitVec 64) := (Sail.BitVec.updateSubrange unusedbits_mask 54 bottom_PAC_bit (Ones (n := ((54 -i bottom_PAC_bit) +i 1))))
      let unusedbits_mask : (BitVec 64) :=
        if (tbi : Bool)
        then (Sail.BitVec.updateSubrange unusedbits_mask 63 56 (Ones (n := 8)))
        else
          (if (mtx : Bool)
          then (Sail.BitVec.updateSubrange unusedbits_mask 63 60 (Ones (n := 4)))
          else unusedbits_mask)
      let PAC ← (( do
        if (((! (IsZero (ptr &&& unusedbits_mask))) && ((ptr &&& unusedbits_mask) != unusedbits_mask)) : Bool)
        then
          (do
            if ((← (HaveEnhancedPAC ())) : Bool)
            then (pure 0x0000000000000000#64)
            else
              (do
                if ((! (← (HaveEnhancedPAC2 ()))) : Bool)
                then (pure (BitVec.update PAC (top_bit -i 1) (Bit (Complement.complement (BitVec.join1 [(BitVec.access PAC (top_bit -i 1))])))))
                else (pure PAC)))
        else (pure PAC) ) : SailM (BitVec 64) )
      if ((! (← (HaveEnhancedPAC2 ()))) : Bool)
      then
        (do
          if (tbi : Bool)
          then
            (do
              sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21787.84-21787.85"
              (pure ((((Sail.BitVec.extractLsb ptr 63 56) +++ selbit) +++ (Sail.BitVec.extractLsb PAC 54 bottom_PAC_bit)) +++ (Sail.BitVec.extractLsb ptr (bottom_PAC_bit -i 1) 0))))
          else
            (do
              sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21790.84-21790.85"
              let result : (BitVec 64) := ((((Sail.BitVec.extractLsb PAC 63 56) +++ selbit) +++ (Sail.BitVec.extractLsb PAC 54 bottom_PAC_bit)) +++ (Sail.BitVec.extractLsb ptr (bottom_PAC_bit -i 1) 0))
              sail_assert (! mtx) "src/v8_base.sail:21792.32-21792.33"
              (pure result)))
      else
        (do
          if (tbi : Bool)
          then
            (do
              sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21796.84-21796.85"
              (pure ((((Sail.BitVec.extractLsb ptr 63 56) +++ selbit) +++ ((Sail.BitVec.extractLsb ptr 54 bottom_PAC_bit) ^^^ (Sail.BitVec.extractLsb PAC 54 bottom_PAC_bit))) +++ (Sail.BitVec.extractLsb ptr (bottom_PAC_bit -i 1) 0))))
          else
            (do
              if (mtx : Bool)
              then
                (do
                  sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21799.84-21799.85"
                  (pure ((((((Sail.BitVec.extractLsb ptr 63 60) ^^^ (Sail.BitVec.extractLsb PAC 63 60)) +++ (Sail.BitVec.extractLsb ptr 59 56)) +++ selbit) +++ ((Sail.BitVec.extractLsb ptr 54 bottom_PAC_bit) ^^^ (Sail.BitVec.extractLsb PAC 54 bottom_PAC_bit))) +++ (Sail.BitVec.extractLsb ptr (bottom_PAC_bit -i 1) 0))))
              else
                (do
                  sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21802.84-21802.85"
                  (pure (((((Sail.BitVec.extractLsb ptr 63 56) ^^^ (Sail.BitVec.extractLsb PAC 63 56)) +++ selbit) +++ ((Sail.BitVec.extractLsb ptr 54 bottom_PAC_bit) ^^^ (Sail.BitVec.extractLsb PAC 54 bottom_PAC_bit))) +++ (Sail.BitVec.extractLsb ptr (bottom_PAC_bit -i 1) 0)))))))

/-- Type quantifiers: k_is_combined : Bool -/
def AuthDA (x : (BitVec 64)) (y : (BitVec 64)) (is_combined : Bool) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let APDAKey_EL1 ← (( do (pure ((Sail.BitVec.extractLsb (← readReg APDAKeyHi_EL1) 63 0) +++ (Sail.BitVec.extractLsb (← readReg APDAKeyLo_EL1) 63 0))) ) : SailM (BitVec 128) )
  let (Enable, TrapEL2, TrapEL3) ← (( do
    let questionMark ← do (pure (← readReg PSTATE).EL)
    let (Enable, TrapEL2, TrapEL3) ← (( do
      if ((questionMark == EL0) : Bool)
      then
        (do
          let IsEL1Regime ← (( do (pure ((← (S1TranslationRegime__1 ())) == EL1)) ) : SailM Bool )
          let Enable ←
            if (IsEL1Regime : Bool)
            then (pure (_get_SCTLR_EL1_Type_EnDA (← readReg SCTLR_EL1)))
            else (pure (_get_SCTLR_EL2_Type_EnDA (← readReg SCTLR_EL2)))
          let TrapEL2 ← (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_API (← readReg HCR_EL2)) == 0#1))) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1)) <||> (do (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))
          let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
          (pure (Enable, TrapEL2, TrapEL3)))
      else
        (do
          let (Enable, TrapEL2, TrapEL3) ← (( do
            if ((questionMark == EL1) : Bool)
            then
              (do
                let Enable ← (pure (_get_SCTLR_EL1_Type_EnDA (← readReg SCTLR_EL1)))
                let TrapEL2 ← (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_API (← readReg HCR_EL2)) == 0#1)))
                let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
                (pure (Enable, TrapEL2, TrapEL3)))
            else
              (do
                let (Enable, TrapEL2, TrapEL3) ← (( do
                  if ((questionMark == EL2) : Bool)
                  then
                    (do
                      let Enable ← (pure (_get_SCTLR_EL2_Type_EnDA (← readReg SCTLR_EL2)))
                      let TrapEL2 : Bool := false
                      let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
                      (pure (Enable, TrapEL2, TrapEL3)))
                  else
                    (do
                      let (Enable, TrapEL2, TrapEL3) ← (( do
                        if ((questionMark == EL3) : Bool)
                        then
                          (do
                            let Enable ← (pure (_get_SCTLR_EL3_Type_EnDA (← readReg SCTLR_EL3)))
                            let TrapEL2 : Bool := false
                            let TrapEL3 : Bool := false
                            (pure (Enable, TrapEL2, TrapEL3)))
                        else (pure (Enable, TrapEL2, TrapEL3)) ) : SailM ((BitVec 1) × Bool × Bool) )
                      (pure (Enable, TrapEL2, TrapEL3))) ) : SailM ((BitVec 1) × Bool × Bool) )
                (pure (Enable, TrapEL2, TrapEL3))) ) : SailM ((BitVec 1) × Bool × Bool) )
          (pure (Enable, TrapEL2, TrapEL3))) ) : SailM ((BitVec 1) × Bool × Bool) )
    (pure (Enable, TrapEL2, TrapEL3)) ) : SailM ((BitVec 1) × Bool × Bool) )
  if ((Enable == 0#1) : Bool)
  then (pure x)
  else
    (do
      if ((←((pure TrapEL3) <&&> (do
           (EL3SDDUndefPriority ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (TrapEL2 : Bool)
          then
            (do
              (TrapPACUse EL2)
              (undefined_bitvector 64))
          else
            (do
              if (TrapEL3 : Bool)
              then
                (do
                  if ((← (EL3SDDUndef ())) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (TrapPACUse EL3)
                      (undefined_bitvector 64)))
              else (Auth x y APDAKey_EL1 true 0#1 is_combined))))

/-- Type quantifiers: k_is_combined : Bool -/
def AuthDB (x : (BitVec 64)) (y : (BitVec 64)) (is_combined : Bool) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let APDBKey_EL1 ← (( do (pure ((Sail.BitVec.extractLsb (← readReg APDBKeyHi_EL1) 63 0) +++ (Sail.BitVec.extractLsb (← readReg APDBKeyLo_EL1) 63 0))) ) : SailM (BitVec 128) )
  let (Enable, TrapEL2, TrapEL3) ← (( do
    let questionMark ← do (pure (← readReg PSTATE).EL)
    let (Enable, TrapEL2, TrapEL3) ← (( do
      if ((questionMark == EL0) : Bool)
      then
        (do
          let IsEL1Regime ← (( do (pure ((← (S1TranslationRegime__1 ())) == EL1)) ) : SailM Bool )
          let Enable ←
            if (IsEL1Regime : Bool)
            then (pure (_get_SCTLR_EL1_Type_EnDB (← readReg SCTLR_EL1)))
            else (pure (_get_SCTLR_EL2_Type_EnDB (← readReg SCTLR_EL2)))
          let TrapEL2 ← (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_API (← readReg HCR_EL2)) == 0#1))) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1)) <||> (do (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))
          let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
          (pure (Enable, TrapEL2, TrapEL3)))
      else
        (do
          let (Enable, TrapEL2, TrapEL3) ← (( do
            if ((questionMark == EL1) : Bool)
            then
              (do
                let Enable ← (pure (_get_SCTLR_EL1_Type_EnDB (← readReg SCTLR_EL1)))
                let TrapEL2 ← (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_API (← readReg HCR_EL2)) == 0#1)))
                let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
                (pure (Enable, TrapEL2, TrapEL3)))
            else
              (do
                let (Enable, TrapEL2, TrapEL3) ← (( do
                  if ((questionMark == EL2) : Bool)
                  then
                    (do
                      let Enable ← (pure (_get_SCTLR_EL2_Type_EnDB (← readReg SCTLR_EL2)))
                      let TrapEL2 : Bool := false
                      let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
                      (pure (Enable, TrapEL2, TrapEL3)))
                  else
                    (do
                      let (Enable, TrapEL2, TrapEL3) ← (( do
                        if ((questionMark == EL3) : Bool)
                        then
                          (do
                            let Enable ← (pure (_get_SCTLR_EL3_Type_EnDB (← readReg SCTLR_EL3)))
                            let TrapEL2 : Bool := false
                            let TrapEL3 : Bool := false
                            (pure (Enable, TrapEL2, TrapEL3)))
                        else (pure (Enable, TrapEL2, TrapEL3)) ) : SailM ((BitVec 1) × Bool × Bool) )
                      (pure (Enable, TrapEL2, TrapEL3))) ) : SailM ((BitVec 1) × Bool × Bool) )
                (pure (Enable, TrapEL2, TrapEL3))) ) : SailM ((BitVec 1) × Bool × Bool) )
          (pure (Enable, TrapEL2, TrapEL3))) ) : SailM ((BitVec 1) × Bool × Bool) )
    (pure (Enable, TrapEL2, TrapEL3)) ) : SailM ((BitVec 1) × Bool × Bool) )
  if ((Enable == 0#1) : Bool)
  then (pure x)
  else
    (do
      if ((←((pure TrapEL3) <&&> (do
           (EL3SDDUndefPriority ())))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (TrapEL2 : Bool)
          then
            (do
              (TrapPACUse EL2)
              (undefined_bitvector 64))
          else
            (do
              if (TrapEL3 : Bool)
              then
                (do
                  if ((← (EL3SDDUndef ())) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (TrapPACUse EL3)
                      (undefined_bitvector 64)))
              else (Auth x y APDBKey_EL1 true 1#1 is_combined))))

/-- Type quantifiers: n : Int, part : Int, width : Nat, width ≥ 0 -/
def Vpart_read (n : Int) (part : Int) (width : Nat) : SailM (BitVec width) := do
  sail_assert ((n ≥b 0) && (n ≤b 31)) "src/v8_base.sail:22343.27-22343.28"
  sail_assert ((part == 0) || (part == 1)) "src/v8_base.sail:22344.32-22344.33"
  if ((part == 0) : Bool)
  then
    (do
      sail_assert (width <b 128) "src/v8_base.sail:22346.26-22346.27"
      sail_assert (((((width == 8) || (width == 16)) || (width == 32)) || (width == 64)) || (width == 128)) "src/v8_base.sail:22347.57-22347.58"
      (V_read n width))
  else
    (do
      sail_assert ((width == 32) || (width == 64)) "src/v8_base.sail:22350.40-22350.41"
      let vreg ← (( do (V_read n 128) ) : SailM (BitVec 128) )
      (pure (Sail.BitVec.extractLsb vreg ((width *i 2) -i 1) width)))

/-- Type quantifiers: n : Int, part : Int, width : Nat, width ≥ 0 -/
def Vpart_set (n : Int) (part : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  sail_assert ((n ≥b 0) && (n ≤b 31)) "src/v8_base.sail:22361.27-22361.28"
  sail_assert ((part == 0) || (part == 1)) "src/v8_base.sail:22362.32-22362.33"
  if ((part == 0) : Bool)
  then
    (do
      sail_assert (width <b 128) "src/v8_base.sail:22364.26-22364.27"
      sail_assert (((((width == 8) || (width == 16)) || (width == 32)) || (width == 64)) || (width == 128)) "src/v8_base.sail:22365.57-22365.58"
      (V_set n width value_name))
  else
    (do
      sail_assert (width == 64) "src/v8_base.sail:22368.26-22368.27"
      let vreg ← (( do (V_read n 64) ) : SailM (BitVec 64) )
      (V_set n 128 ((Sail.BitVec.extractLsb value_name 63 0) +++ vreg)))

def AArch64_ResetSpecialRegisters (_ : Unit) : SailM Unit := do
  writeReg SP_EL0 (← (__UNKNOWN_bits 64))
  writeReg SP_EL1 (← (__UNKNOWN_bits 64))
  writeReg SPSR_EL1 (Mk_SPSR_EL1_Type (← (__UNKNOWN_bits 64)))
  writeReg ELR_EL1 (← (__UNKNOWN_bits 64))
  if ((HaveEL EL2) : Bool)
  then
    (do
      writeReg SP_EL2 (← (__UNKNOWN_bits 64))
      writeReg SPSR_EL2 (Mk_SPSR_EL2_Type (← (__UNKNOWN_bits 64)))
      writeReg ELR_EL2 (← (__UNKNOWN_bits 64)))
  else (pure ())
  if ((HaveEL EL3) : Bool)
  then
    (do
      writeReg SP_EL3 (← (__UNKNOWN_bits 64))
      writeReg SPSR_EL3 (Mk_SPSR_EL3_Type (← (__UNKNOWN_bits 64)))
      writeReg ELR_EL3 (← (__UNKNOWN_bits 64)))
  else (pure ())
  if ((HaveAArch32EL EL1) : Bool)
  then
    (do
      writeReg SPSR_fiq (Sail.BitVec.updateSubrange (← readReg SPSR_fiq) 31 0 (← (__UNKNOWN_bits 32)))
      writeReg SPSR_irq (Sail.BitVec.updateSubrange (← readReg SPSR_irq) 31 0 (← (__UNKNOWN_bits 32)))
      writeReg SPSR_abt (Sail.BitVec.updateSubrange (← readReg SPSR_abt) 31 0 (← (__UNKNOWN_bits 32)))
      writeReg SPSR_und (Sail.BitVec.updateSubrange (← readReg SPSR_und) 31 0 (← (__UNKNOWN_bits 32))))
  else (pure ())
  writeReg DLR_EL0 (← (__UNKNOWN_bits 64))
  writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type (← (__UNKNOWN_bits 64)))

def ELR_read__1 (_ : Unit) : SailM (BitVec 64) := do
  sail_assert ((← readReg PSTATE).EL != EL0) "src/v8_base.sail:22444.27-22444.28"
  (ELR_read (← readReg PSTATE).EL)

def _set_CNTKCTL_Type_PL0PCTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_Type_PL0PCTEN r v)

def _set_CNTKCTL_Type_PL0PTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_Type_PL0PTEN r v)

def _set_CNTKCTL_Type_PL0VCTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_Type_PL0VCTEN r v)

def _set_CNTKCTL_Type_PL0VTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTKCTL_Type_PL0VTEN r v)

def _set_GCR_EL1_Type_Exclude (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCR_EL1_Type_Exclude r v)

def _set_GCR_EL1_Type_RRND (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GCR_EL1_Type_RRND r v)

def _set_RGSR_EL1_Type_SEED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 48)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RGSR_EL1_Type_SEED r v)

def _set_RGSR_EL1_Type_TAG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RGSR_EL1_Type_TAG r v)

def AArch64_NextRandomTagBit (_ : Unit) : SailM (BitVec 1) := do
  sail_assert ((_get_GCR_EL1_Type_RRND (← readReg GCR_EL1)) == 0#1) "src/v8_base.sail:22689.31-22689.32"
  let lfsr ← (( do (pure (Sail.BitVec.extractLsb (_get_RGSR_EL1_Type_SEED (← readReg RGSR_EL1)) 15 0)) ) : SailM (BitVec 16) )
  let top : (BitVec 1) := ((((BitVec.join1 [(BitVec.access lfsr 5)]) ^^^ (BitVec.join1 [(BitVec.access lfsr 3)])) ^^^ (BitVec.join1 [(BitVec.access lfsr 2)])) ^^^ (BitVec.join1 [(BitVec.access lfsr 0)]))
  writeReg RGSR_EL1 (Sail.BitVec.updateSubrange (← readReg RGSR_EL1) 55 8 (Sail.BitVec.updateSubrange (Sail.BitVec.extractLsb (← readReg RGSR_EL1) 55 8) 15 0 (top +++ (Sail.BitVec.extractLsb lfsr 15 1))))
  (pure top)

def _set_TFSRE0_EL1_Type_TF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSRE0_EL1_Type_TF0 r v)

def _set_TFSR_EL1_Type_TF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSR_EL1_Type_TF0 r v)

def _set_TFSR_EL2_Type_TF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSR_EL2_Type_TF0 r v)

def _set_TFSR_EL3_Type_TF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSR_EL3_Type_TF0 r v)

def _set_TFSRE0_EL1_Type_TF1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSRE0_EL1_Type_TF1 r v)

def _set_TFSR_EL1_Type_TF1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSR_EL1_Type_TF1 r v)

def _set_TFSR_EL2_Type_TF1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TFSR_EL2_Type_TF1 r v)

def _set_DBGBCR_EL1_Type_BAS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_BAS r v)

def _set_DBGBCR_Type_BAS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_Type_BAS r v)

def _set_DBGWCR_EL1_Type_BAS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_BAS r v)

def _set_DBGWCR_Type_BAS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_Type_BAS r v)

def _set_DBGBCR_EL1_Type_BT2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_BT2 r v)

def _set_DBGBCR_EL1_Type_HMC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_HMC r v)

def _set_DBGBCR_Type_HMC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_Type_HMC r v)

def _set_DBGWCR_EL1_Type_HMC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_HMC r v)

def _set_DBGWCR_Type_HMC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_Type_HMC r v)

def _set_DBGBCR_EL1_Type_LBN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_LBN r v)

def _set_DBGBCR_Type_LBN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_Type_LBN r v)

def _set_DBGWCR_EL1_Type_LBN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_LBN r v)

def _set_DBGWCR_Type_LBN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_Type_LBN r v)

def _set_DBGBCR_EL1_Type_LBNX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_LBNX r v)

def _set_DBGWCR_EL1_Type_LBNX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_LBNX r v)

def _set_DBGBCR_EL1_Type_MASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_MASK r v)

def _set_DBGWCR_EL1_Type_MASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_MASK r v)

def _set_DBGWCR_Type_MASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_Type_MASK r v)

def _set_DBGBCR_EL1_Type_PMC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_PMC r v)

def _set_DBGBCR_Type_PMC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_Type_PMC r v)

def _set_DBGBCR_EL1_Type_SSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_SSC r v)

def _set_DBGBCR_Type_SSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_Type_SSC r v)

def _set_DBGWCR_EL1_Type_SSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_SSC r v)

def _set_DBGWCR_Type_SSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_Type_SSC r v)

def _set_DBGBCR_EL1_Type_SSCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_SSCE r v)

def _set_DBGWCR_EL1_Type_SSCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_SSCE r v)

def _set_DBGBVR_EL1_Type_ContextID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_ContextID r v)

def _set_DBGBVR_Type_ContextID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBVR_Type_ContextID r v)

def _set_DBGBVR_EL1_Type_ContextID2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_ContextID2 r v)

def _set_DBGBXVR_Type_ContextID2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBXVR_Type_ContextID2 r v)

def _set_DBGBVR_EL1_Type_RESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 15)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_RESS r v)

def _set_DBGWVR_EL1_Type_RESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 15)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWVR_EL1_Type_RESS r v)

def _set_VNCR_EL2_Type_RESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 7)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VNCR_EL2_Type_RESS r v)

def _set_DBGBVR_EL1_Type_VMID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_VMID r v)

def _set_DBGBXVR_Type_VMID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGBXVR_Type_VMID r v)

def _set_EDVIDSR_Type_VMID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDVIDSR_Type_VMID r v)

def _set_PMVCIDSR_Type_VMID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMVCIDSR_Type_VMID r v)

def _set_PMVIDSR_Type_VMID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMVIDSR_Type_VMID r v)

def _set_VTTBR_EL2_Type_VMID (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTTBR_EL2_Type_VMID r v)

def _set_VTTBR_Type_VMID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTTBR_Type_VMID r v)

def _set_VTCR_EL2_Type_GCSH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_GCSH r v)

def _set_VTCR_EL2_Type_NSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_NSA r v)

def _set_VTCR_EL2_Type_NSW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_NSW r v)

def _set_VTCR_EL2_Type_S2PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_S2PIE r v)

def _set_ID_AA64MMFR3_EL1_Type_S2PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_S2PIE r v)

def _set_VTCR_EL2_Type_S2POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_S2POE r v)

def _set_ID_AA64MMFR3_EL1_Type_S2POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_S2POE r v)

def _set_VTCR_EL2_Type_SL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_SL0 r v)

def _set_VSTCR_EL2_Type_SL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSTCR_EL2_Type_SL0 r v)

def _set_VTCR_Type_SL0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_Type_SL0 r v)

def _set_VTCR_EL2_Type_SL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_SL2 r v)

def _set_VSTCR_EL2_Type_SL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSTCR_EL2_Type_SL2 r v)

def _set_VTCR_EL2_Type_TL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_TL0 r v)

def _set_VTCR_EL2_Type_TL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_TL1 r v)

def _set_VTCR_EL2_Type_VS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VTCR_EL2_Type_VS r v)

def _set_DBGWCR_EL1_Type_LSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_LSC r v)

def _set_DBGWCR_Type_LSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_Type_LSC r v)

def _set_DBGWCR_EL1_Type_PAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_PAC r v)

def _set_DBGWCR_Type_PAC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_Type_PAC r v)

def _set_DBGWCR_EL1_Type_WT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_WT r v)

def _set_DBGWCR_Type_WT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGWCR_Type_WT r v)

def _set_PMCFGR_Type_WT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_WT r v)

def _set_MECID_P0_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECID_P0_EL2_Type_MECID r v)

def _set_MECID_A0_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECID_A0_EL2_Type_MECID r v)

def _set_MECID_A1_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECID_A1_EL2_Type_MECID r v)

def _set_MECID_P1_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECID_P1_EL2_Type_MECID r v)

def _set_MECID_RL_A_EL3_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECID_RL_A_EL3_Type_MECID r v)

def _set_VMECID_A_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMECID_A_EL2_Type_MECID r v)

def _set_VMECID_P_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMECID_P_EL2_Type_MECID r v)

def _set_VSTCR_EL2_Type_SW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSTCR_EL2_Type_SW r v)

def _set_FPSID_Type_SW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSID_Type_SW r v)

def _set_PMUSERENR_EL0_Type_SW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_SW r v)

def _set_PMUSERENR_Type_SW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_Type_SW r v)

def ProtectionEnabled (el : (BitVec 2)) : SailM Bool := SailME.run do
  sail_assert (HaveEL el) "src/v8_base.sail:28475.21-28475.22"
  let regime ← (( do (S1TranslationRegime el) ) : SailME Bool (BitVec 2) )
  sail_assert (! (← (ELUsingAArch32 regime))) "src/v8_base.sail:28477.43-28477.44"
  if ((! (← (IsD128Enabled el))) : Bool)
  then
    (do
      let questionMark := regime
      if ((questionMark == EL1) : Bool)
      then SailME.throw (← (do (IsTCR2EL1Enabled ()) <&&> (do (pure ((_get_TCR2_EL1_Type_PnCH (← readReg TCR2_EL1)) == 1#1)))))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then SailME.throw (← (do (IsTCR2EL2Enabled ()) <&&> (do (pure ((_get_TCR2_EL2_Type_PnCH (← readReg TCR2_EL2)) == 1#1)))))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then SailME.throw (← (do (pure ((_get_TCR_EL3_Type_PnCH (← readReg TCR_EL3)) == 1#1))))
              else (pure ())))
      (pure false))
  else (pure true)

def _set_RCWMASK_EL1_Type_Mask (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RCWMASK_EL1_Type_Mask r v)

def _set_RCWSMASK_EL1_Type_Software_Mask (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RCWSMASK_EL1_Type_Software_Mask r v)

def AArch64_MemTag_read (address : (BitVec 64)) (accdesc_in : AccessDescriptor) : SailM (BitVec 4) := do
  let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
  let tag ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  sail_assert (accdesc_in.tagaccess && (! accdesc_in.tagchecked)) "src/v8_base.sail:28695.65-28695.66"
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := true
  let accdesc ← (( do
    if ((← (HaveMTE2Ext ())) : Bool)
    then (do (pure { accdesc with tagaccess := ← (do (AArch64_AllocationTagAccessIsEnabled accdesc.el)) }))
    else (pure accdesc) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned TAG_GRANULE) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then (AArch64_Abort address memaddrdesc.fault)
  else (pure ())
  if ((accdesc.tagaccess && (BEq.beq memaddrdesc.memattrs.tags MemTag_AllocationTagged)) : Bool)
  then
    (do
      let (memstatus, tag) ← (( do
        let (tup__0, tup__1) ← do (PhysMemTagRead memaddrdesc accdesc)
        let memstatus : PhysMemRetStatus := tup__0
        let tag : (BitVec 4) := tup__1
        (pure (memstatus, tag)) ) : SailM (PhysMemRetStatus × (BitVec 4)) )
      if ((IsFault__2 memstatus) : Bool)
      then (HandleExternalReadAbort memstatus memaddrdesc 1 accdesc)
      else (pure ())
      (pure tag))
  else
    (do
      if ((((← (HaveMTECanonicalTagCheckingExt ())) && accdesc.tagaccess) && (BEq.beq memaddrdesc.memattrs.tags MemTag_CanonicallyTagged)) : Bool)
      then
        (if (((BitVec.join1 [(BitVec.access address 55)]) == 0#1) : Bool)
        then (pure 0b0000#4)
        else (pure 0b1111#4))
      else (pure 0b0000#4))

def AArch64_MemTag_set (address : (BitVec 64)) (accdesc_in : AccessDescriptor) (value_name : (BitVec 4)) : SailM Unit := do
  let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
  sail_assert (accdesc_in.tagaccess && (! accdesc_in.tagchecked)) "src/v8_base.sail:28724.65-28724.66"
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address TAG_GRANULE)
  if ((! aligned) : Bool)
  then (AArch64_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let accdesc ← (( do
    if ((← (HaveMTE2Ext ())) : Bool)
    then (do (pure { accdesc with tagaccess := ← (do (AArch64_AllocationTagAccessIsEnabled accdesc.el)) }))
    else (pure accdesc) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned TAG_GRANULE) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then (AArch64_Abort address memaddrdesc.fault)
  else (pure ())
  if ((accdesc.tagaccess && (BEq.beq memaddrdesc.memattrs.tags MemTag_AllocationTagged)) : Bool)
  then
    (do
      let memstatus ← (( do (PhysMemTagWrite memaddrdesc accdesc value_name) ) : SailM PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then (HandleExternalWriteAbort memstatus memaddrdesc 1 accdesc)
      else (pure ()))
  else (pure ())

/-- Type quantifiers: N : Nat, offset : Int, List.elem N [64, 128] -/
def NVMem_read__1 (offset : Int) (N : Nat) : SailM (BitVec N) := do
  sail_assert (offset >b 0) "src/v8_base.sail:28763.21-28763.22"
  sail_assert ((N == 64) || (N == 128)) "src/v8_base.sail:28764.29-28764.30"
  let address ← (( do (pure (sign_extend ((_get_VNCR_EL2_Type_BADDR (← readReg VNCR_EL2)) +++ (integer_subrange offset 11 0)) 64)) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescNV2 MemOp_LOAD) ) : SailM AccessDescriptor )
  (Mem_read address (Int.ediv N 8) accdesc)

/-- Type quantifiers: N : Nat, offset : Int, List.elem N [64, 128] -/
def NVMem_set__1 (offset : Int) (N : Nat) (value_name : (BitVec N)) : SailM Unit := do
  sail_assert (offset >b 0) "src/v8_base.sail:28783.21-28783.22"
  sail_assert ((N == 64) || (N == 128)) "src/v8_base.sail:28784.29-28784.30"
  let address ← (( do (pure (sign_extend ((_get_VNCR_EL2_Type_BADDR (← readReg VNCR_EL2)) +++ (integer_subrange offset 11 0)) 64)) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescNV2 MemOp_STORE) ) : SailM AccessDescriptor )
  (Mem_set address (Int.ediv N 8) accdesc value_name)

def MemStore64B (address : (BitVec 64)) (value_name : (BitVec 512)) (accdesc_in : AccessDescriptor) : SailM Unit := do
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let size := 64
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address size)
  if ((←((pure (! aligned)) <&&> (do
       (AArch64_UnalignedAccessFaults accdesc address size)))) : Bool)
  then (AArch64_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let accdesc ← (( do
    if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
    then (do (pure { accdesc with tagchecked := ← (do (AArch64_AccessIsTagChecked address accdesc)) }))
    else (pure accdesc) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then (AArch64_Abort address memaddrdesc.fault)
  else (pure ())
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) 64)
    else ()
  if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
  then
    (do
      let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
      if ((! (← (AArch64_CheckTag memaddrdesc accdesc ptag))) : Bool)
      then (AArch64_TagCheckFault address accdesc)
      else (pure ()))
  else (pure ())
  let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
  if ((! (← (AddressSupportsLS64 memaddrdesc.paddress.address))) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_LS64UNSUPPORTED) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_LIMITED_ATOMICITY) || (BEq.beq c Constraint_FAULT)) "src/v8_base.sail:28823.72-28823.73"
      if ((BEq.beq c Constraint_FAULT) : Bool)
      then (AArch64_Abort address (← (ExclusiveFault accdesc)))
      else
        (do
          let (memaddrdesc, memstatus) ← (( do
            let loop_i_lower := 0
            let loop_i_upper := (size -i 1)
            let mut loop_vars := (memaddrdesc, memstatus)
            for i in [loop_i_lower:loop_i_upper:1]i do
              let (memaddrdesc, memstatus) := loop_vars
              loop_vars ← do
                let memstatus ← (PhysMemWrite memaddrdesc 1 accdesc none (Sail.BitVec.extractLsb value_name ((8 *i i) +i 7) (8 *i i)))
                if ((IsFault__2 memstatus) : Bool)
                then (HandleExternalWriteAbort memstatus memaddrdesc 1 accdesc)
                else (pure ())
                let memaddrdesc : AddressDescriptor := { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt memaddrdesc.paddress.address 1) } }
                (pure (memaddrdesc, memstatus))
            (pure loop_vars) ) : SailM (AddressDescriptor × PhysMemRetStatus) )
          (pure ())))
  else
    (do
      let memstatus ← (( do (PhysMemWrite memaddrdesc size accdesc none value_name) ) : SailM PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then (HandleExternalWriteAbort memstatus memaddrdesc size accdesc)
      else (pure ()))

def MemLoad64B (address : (BitVec 64)) (accdesc_in : AccessDescriptor) : SailM (BitVec 512) := do
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let data ← (( do (undefined_bitvector 512) ) : SailM (BitVec 512) )
  let size := 64
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address size)
  if ((←((pure (! aligned)) <&&> (do
       (AArch64_UnalignedAccessFaults accdesc address size)))) : Bool)
  then (AArch64_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let accdesc ← (( do
    if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
    then (do (pure { accdesc with tagchecked := ← (do (AArch64_AccessIsTagChecked address accdesc)) }))
    else (pure accdesc) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then (AArch64_Abort address memaddrdesc.fault)
  else (pure ())
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) size)
    else ()
  if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
  then
    (do
      let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
      if ((! (← (AArch64_CheckTag memaddrdesc accdesc ptag))) : Bool)
      then (AArch64_TagCheckFault address accdesc)
      else (pure ()))
  else (pure ())
  if ((! (← (AddressSupportsLS64 memaddrdesc.paddress.address))) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_LS64UNSUPPORTED) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_LIMITED_ATOMICITY) || (BEq.beq c Constraint_FAULT)) "src/v8_base.sail:28910.72-28910.73"
      if ((BEq.beq c Constraint_FAULT) : Bool)
      then
        (do
          (AArch64_Abort address (← (ExclusiveFault accdesc)))
          (pure data))
      else
        (do
          let (data, memaddrdesc) ← (( do
            let loop_i_lower := 0
            let loop_i_upper := (size -i 1)
            let mut loop_vars := (data, memaddrdesc)
            for i in [loop_i_lower:loop_i_upper:1]i do
              let (data, memaddrdesc) := loop_vars
              loop_vars ← do
                let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
                let (data, memstatus) ← (( do
                  let (tup__0, tup__1) ← do (PhysMemRead memaddrdesc 1 accdesc none)
                  let memstatus : PhysMemRetStatus := tup__0
                  let data : (BitVec 512) := (Sail.BitVec.updateSubrange data ((8 *i i) +i 7) (8 *i i) tup__1)
                  (pure (data, memstatus)) ) : SailM ((BitVec 512) × PhysMemRetStatus) )
                if ((IsFault__2 memstatus) : Bool)
                then (HandleExternalReadAbort memstatus memaddrdesc 1 accdesc)
                else (pure ())
                let memaddrdesc : AddressDescriptor := { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt memaddrdesc.paddress.address 1) } }
                (pure (data, memaddrdesc))
            (pure loop_vars) ) : SailM ((BitVec 512) × AddressDescriptor) )
          (pure data)))
  else
    (do
      let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
      let (data, memstatus) ← (( do
        let (tup__0, tup__1) ← do (PhysMemRead memaddrdesc size accdesc none)
        let memstatus : PhysMemRetStatus := tup__0
        let data : (BitVec 512) := tup__1
        (pure (data, memstatus)) ) : SailM ((BitVec 512) × PhysMemRetStatus) )
      if ((IsFault__2 memstatus) : Bool)
      then (HandleExternalReadAbort memstatus memaddrdesc size accdesc)
      else (pure ())
      (pure data))

/-- Type quantifiers: size : Int -/
def AArch64_TagMemZero (regval : (BitVec 64)) (vaddress : (BitVec 64)) (accdesc_in : AccessDescriptor) (size : Int) : SailM Unit := do
  let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
  sail_assert (accdesc_in.tagaccess && (! accdesc_in.tagchecked)) "src/v8_base.sail:29013.65-29013.66"
  let accdesc : AccessDescriptor := accdesc_in
  let count := (Int.shiftr size LOG2_TAG_GRANULE)
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress vaddress)
  let aligned : Bool := (IsAligned__1 vaddress TAG_GRANULE)
  if ((! aligned) : Bool)
  then (AArch64_Abort vaddress (← (AlignmentFault accdesc)))
  else (pure ())
  let accdesc ← (( do
    if ((← (HaveMTE2Ext ())) : Bool)
    then (do (pure { accdesc with tagaccess := ← (do (AArch64_AllocationTagAccessIsEnabled accdesc.el)) }))
    else (pure accdesc) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      if ((← (IsDebugException memaddrdesc.fault)) : Bool)
      then (AArch64_Abort vaddress memaddrdesc.fault)
      else (AArch64_Abort regval memaddrdesc.fault))
  else (pure ())
  if (((! accdesc.tagaccess) || (bne memaddrdesc.memattrs.tags MemTag_AllocationTagged)) : Bool)
  then (pure ())
  else
    (do
      let (memaddrdesc, memstatus) ← (( do
        let loop_i_lower := 0
        let loop_i_upper := (count -i 1)
        let mut loop_vars := (memaddrdesc, memstatus)
        for i in [loop_i_lower:loop_i_upper:1]i do
          let (memaddrdesc, memstatus) := loop_vars
          loop_vars ← do
            let memstatus ← (PhysMemTagWrite memaddrdesc accdesc tag)
            if ((IsFault__2 memstatus) : Bool)
            then (HandleExternalWriteAbort memstatus memaddrdesc 1 accdesc)
            else (pure ())
            let memaddrdesc : AddressDescriptor := { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt memaddrdesc.paddress.address TAG_GRANULE) } }
            (pure (memaddrdesc, memstatus))
        (pure loop_vars) ) : SailM (AddressDescriptor × PhysMemRetStatus) )
      (pure ()))

/-- Type quantifiers: size : Int -/
def AArch64_SetExclusiveMonitors (address : (BitVec 64)) (size : Int) : SailM Unit := do
  writeReg __ExclusiveMonitorSet true
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_LOAD acqrel tagchecked) ) : SailM AccessDescriptor )
  let aligned : Bool := (IsAligned__1 address size)
  if ((←((pure (! aligned)) <&&> (do
       (AArch64_UnalignedAccessFaults accdesc address size)))) : Bool)
  then (AArch64_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then (pure ())
  else
    (let _ : Unit :=
      if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
      then (MarkExclusiveGlobal memaddrdesc.paddress (ProcessorID ()) size)
      else ()
    let _ : Unit := (MarkExclusiveLocal memaddrdesc.paddress (ProcessorID ()) size)
    (pure (AArch64_MarkExclusiveVA address (ProcessorID ()) size)))

/-- Type quantifiers: size : Int -/
def AArch64_ExclusiveMonitorsPass (address : (BitVec 64)) (size : Int) : SailM Bool := do
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_STORE acqrel tagchecked) ) : SailM AccessDescriptor )
  let aligned : Bool := (IsAligned__1 address size)
  if ((←((pure (! aligned)) <&&> (do
       (AArch64_UnalignedAccessFaults accdesc address size)))) : Bool)
  then (AArch64_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  if ((! (AArch64_IsExclusiveVA address (ProcessorID ()) size)) : Bool)
  then (pure false)
  else
    (do
      let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailM AddressDescriptor )
      if ((IsFault memaddrdesc) : Bool)
      then (AArch64_Abort address memaddrdesc.fault)
      else (pure ())
      let passed : Bool := (IsExclusiveLocal memaddrdesc.paddress (ProcessorID ()) size)
      let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
      if ((passed && (bne memaddrdesc.memattrs.shareability Shareability_NSH)) : Bool)
      then (pure (IsExclusiveGlobal memaddrdesc.paddress (ProcessorID ()) size))
      else (pure passed))

def CheckSMEZT0Enabled (_ : Unit) : SailM Unit := do
  if (((← readReg PSTATE).ZA == 0#1) : Bool)
  then (SMEAccessTrap SMEExceptionType_InactiveZA (← readReg PSTATE).EL)
  else (pure ())
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
       (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
       (pure (! (← (IsInHost ()))))))) : Bool)
  then
    (do
      if (((_get_SMCR_EL1_Type_EZT0 (← readReg SMCR_EL1)) == 0#1) : Bool)
      then (SMEAccessTrap SMEExceptionType_InaccessibleZT0 EL1)
      else (pure ()))
  else (pure ())
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
       (pure ((← readReg PSTATE).EL == EL1)) <||> (do
         (pure ((← readReg PSTATE).EL == EL2)))) <&&> (do
       (EL2Enabled ())))) : Bool)
  then
    (do
      if (((_get_SMCR_EL2_Type_EZT0 (← readReg SMCR_EL2)) == 0#1) : Bool)
      then (SMEAccessTrap SMEExceptionType_InaccessibleZT0 EL2)
      else (pure ()))
  else (pure ())
  if ((HaveEL EL3) : Bool)
  then
    (do
      if (((_get_SMCR_EL3_Type_EZT0 (← readReg SMCR_EL3)) == 0#1) : Bool)
      then (SMEAccessTrap SMEExceptionType_InaccessibleZT0 EL3)
      else (pure ()))
  else (pure ())

def CheckSMEAccess (_ : Unit) : SailM Unit := do
  let disabled ← (( do (undefined_bool ()) ) : SailM Bool )
  let disabled ← (( do
    if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
         (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
         (pure (! (← (IsInHost ()))))))) : Bool)
    then
      (do
        let disabled ← (( do
          let b__0 ← do (pure (_get_CPACR_EL1_Type_SMEN (← readReg CPACR_EL1)))
          if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
          then (pure true)
          else
            (do
              if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
              then (do (pure ((← readReg PSTATE).EL == EL0)))
              else (pure false)) ) : SailM Bool )
        if (disabled : Bool)
        then (SMEAccessTrap SMEExceptionType_AccessTrap EL1)
        else (pure ())
        (pure disabled))
    else (pure disabled) ) : SailM Bool )
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
       (pure ((← readReg PSTATE).EL == EL1)) <||> (do
         (pure ((← readReg PSTATE).EL == EL2)))) <&&> (do
       (EL2Enabled ())))) : Bool)
  then
    (do
      if ((←((HaveVirtHostExt ()) <&&> (do
           (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))) : Bool)
      then
        (do
          let disabled ← (( do
            let b__2 ← do (pure (_get_CPTR_EL2_Type_SMEN (← readReg CPTR_EL2)))
            if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
            then (pure true)
            else
              (do
                if ((b__2 == (0b01#2 : (BitVec 2))) : Bool)
                then (do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))
                else (pure false)) ) : SailM Bool )
          if (disabled : Bool)
          then (SMEAccessTrap SMEExceptionType_AccessTrap EL2)
          else (pure ()))
      else
        (do
          if (((_get_CPTR_EL2_Type_TSM (← readReg CPTR_EL2)) == 1#1) : Bool)
          then (SMEAccessTrap SMEExceptionType_AccessTrap EL2)
          else (pure ())))
  else (pure ())
  if ((HaveEL EL3) : Bool)
  then
    (do
      if (((_get_CPTR_EL3_Type_ESM (← readReg CPTR_EL3)) == 0#1) : Bool)
      then (SMEAccessTrap SMEExceptionType_AccessTrap EL3)
      else (pure ()))
  else (pure ())

def ResetSMEState (_ : Unit) : SailM Unit := do
  let vectors_name := (Int.ediv MAX_VL 8)
  let loop_n_lower := 0
  let loop_n_upper := (vectors_name -i 1)
  let mut loop_vars := ()
  for n in [loop_n_lower:loop_n_upper:1]i do
    let () := loop_vars
    loop_vars ← do writeReg _ZA (vectorUpdate (← readReg _ZA) n (Zeros (n := MAX_VL)))
  (pure loop_vars)
  writeReg _ZT0 (Zeros (n := ZT0_LEN))

/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemNF_read (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) : SailM ((BitVec (8 * size)) × Bool) := SailME.run do
  let c ← (( do (undefined_Constraint ()) ) : SailME ((BitVec (8 * size)) × Bool) Constraint )
  sail_assert ((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16))))) "src/v8_base.sail:29720.69-29720.70"
  let value_name ← (( do (undefined_bitvector (8 *i size)) ) : SailME ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
  let bad ← (( do (undefined_bool ()) ) : SailME ((BitVec (8 * size)) × Bool) Bool )
  let aligned : Bool := (IsAligned__1 address size)
  if ((←((pure (! aligned)) <&&> (do
       (AlignmentEnforced ())))) : Bool)
  then (pure ((← (__UNKNOWN_bits (8 *i size))), true))
  else
    (do
      let atomic : Bool := (aligned || (size == 1))
      let value_name ← (( do
        if ((! atomic) : Bool)
        then
          (do
            let (bad, value_name) ← (( do
              let (tup__0, tup__1) ← do (MemSingleNF_read address 1 accdesc aligned)
              let value_name : (BitVec (8 * size)) := (Sail.BitVec.updateSubrange value_name 7 0 tup__0)
              let bad : Bool := tup__1
              (pure (bad, value_name)) ) : SailME ((BitVec (8 * size)) × Bool) (Bool × (BitVec (8 * size))) )
            if (bad : Bool)
            then SailME.throw (← (do (pure ((← (__UNKNOWN_bits (8 *i size))), true))))
            else
              (do
                let aligned ← (( do
                  if ((! aligned) : Bool)
                  then
                    (do
                      let c ← (( do (ConstrainUnpredictable Unpredictable_DEVPAGE2) ) : SailME ((BitVec (8 * size)) × Bool) Constraint )
                      sail_assert ((BEq.beq c Constraint_FAULT) || (BEq.beq c Constraint_NONE)) "src/v8_base.sail:29735.63-29735.64"
                      if ((BEq.beq c Constraint_NONE) : Bool)
                      then (pure true)
                      else (pure aligned))
                  else (pure aligned) ) : SailME ((BitVec (8 * size)) × Bool) Bool )
                let (bad, value_name) ← (( do
                  let loop_i_lower := 1
                  let loop_i_upper := (size -i 1)
                  let mut loop_vars := (bad, value_name)
                  for i in [loop_i_lower:loop_i_upper:1]i do
                    let (bad, value_name) := loop_vars
                    loop_vars ← do
                      let (bad, value_name) ← (( do
                        let (tup__0, tup__1) ← do (MemSingleNF_read (BitVec.addInt address i) 1 accdesc aligned)
                        let value_name : (BitVec (8 * size)) := (Sail.BitVec.updateSubrange value_name ((8 *i i) +i 7) (8 *i i) tup__0)
                        let bad : Bool := tup__1
                        (pure (bad, value_name)) ) : SailME ((BitVec (8 * size)) × Bool) (Bool × (BitVec (8 * size))) )
                      if (bad : Bool)
                      then SailME.throw (← (do (pure ((← (__UNKNOWN_bits (8 *i size))), true))))
                      else (pure ())
                      (pure (bad, value_name))
                  (pure loop_vars) ) : SailME ((BitVec (8 * size)) × Bool) (Bool × (BitVec (8 * size))) )
                (pure value_name)))
        else
          (do
            let (bad, value_name) ← (( do
              let (tup__0, tup__1) ← do (MemSingleNF_read address size accdesc aligned)
              let value_name : (BitVec (8 * size)) := tup__0
              let bad : Bool := tup__1
              (pure (bad, value_name)) ) : SailME ((BitVec (8 * size)) × Bool) (Bool × (BitVec (8 * size))) )
            if (bad : Bool)
            then SailME.throw (← (do (pure ((← (__UNKNOWN_bits (8 *i size))), true))))
            else (pure ())
            (pure value_name)) ) : SailME ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
      let value_name ← (( do
        if ((← (BigEndian accdesc.acctype)) : Bool)
        then (pure (reverse_endianness value_name))
        else (pure value_name) ) : SailME ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
      let value_name := value_name
      (pure (value_name, false)))

/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def FirstActive (mask : (BitVec k_N)) (x : (BitVec k_N)) (esize : Int) : SailM (BitVec 1) := SailME.run do
  let elements := (fdiv_int (Sail.BitVec.length x) (fdiv_int esize 8))
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then SailME.throw (← (do (PredicateElement x e esize)))
      else (pure ())
  (pure loop_vars)
  (pure 0#1)

/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def LastActive (mask : (BitVec k_N)) (x : (BitVec k_N)) (esize : Int) : SailM (BitVec 1) := SailME.run do
  let elements := (fdiv_int (Sail.BitVec.length x) (fdiv_int esize 8))
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_upper:loop_e_lower:-1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then SailME.throw (← (do (PredicateElement x e esize)))
      else (pure ())
  (pure loop_vars)
  (pure 0#1)

/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def NoneActive (mask : (BitVec k_N)) (x : (BitVec k_N)) (esize : Int) : SailM (BitVec 1) := SailME.run do
  let elements := (fdiv_int (Sail.BitVec.length x) (fdiv_int esize 8))
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((←((ActivePredicateElement mask e esize) <&&> (do
           (ActivePredicateElement x e esize)))) : Bool)
      then SailME.throw (0#1 : (BitVec 1))
      else (pure ())
  (pure loop_vars)
  (pure 1#1)

/-- Type quantifiers: e : Int, esize : Int -/
def ElemFFR_read (e : Int) (esize : Int) : SailM (BitVec 1) := do
  (PredicateElement (← readReg _FFR) e esize)

/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def LastActiveElement (mask : (BitVec k_N)) (esize : Int) : SailM Int := SailME.run do
  let elements := (fdiv_int (Sail.BitVec.length mask) (fdiv_int esize 8))
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_upper:loop_e_lower:-1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then SailME.throw (e : Int)
      else (pure ())
  (pure loop_vars)
  (pure (Neg.neg 1))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPExpA (op : (BitVec k_N)) : SailM (BitVec k_N) := do
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:30724.41-30724.42"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op)) ) : SailM (BitVec k_N) )
  let idx :=
    if (((Sail.BitVec.length result) == 16) : Bool)
    then (BitVec.toNat (Sail.BitVec.extractLsb op 4 0))
    else (BitVec.toNat (Sail.BitVec.extractLsb op 5 0))
  let coeff ← (( do (FPExpCoefficient_read idx (Sail.BitVec.length result)) ) : SailM (BitVec k_N) )
  if (((Sail.BitVec.length result) == 16) : Bool)
  then (pure (Sail.BitVec.updateSubrange result 15 0 ((0#1 +++ (Sail.BitVec.extractLsb op 9 5)) +++ (Sail.BitVec.extractLsb coeff 9 0))))
  else
    (if (((Sail.BitVec.length result) == 32) : Bool)
    then (pure (Sail.BitVec.updateSubrange result 31 0 ((0#1 +++ (Sail.BitVec.extractLsb op 13 6)) +++ (Sail.BitVec.extractLsb coeff 22 0))))
    else (pure (Sail.BitVec.updateSubrange result 63 0 ((0#1 +++ (Sail.BitVec.extractLsb op 16 6)) +++ (Sail.BitVec.extractLsb coeff 51 0)))))

/-- Type quantifiers: esize : Int, slice_name : Int, tile : Int, width : Nat, width ≥ 0 -/
def ZAhslice_read (tile : Int) (esize : Int) (slice_name : Int) (width : Nat) : SailM (BitVec width) := do
  let SVL ← do (CurrentSVL_read ())
  sail_assert ((esize == 8) || ((esize == 16) || ((esize == 32) || ((esize == 64) || (esize == 128))))) "src/v8_base.sail:31159.78-31159.79"
  let tiles := (Int.ediv esize 8)
  sail_assert ((tile ≥b 0) && (tile <b tiles)) "src/v8_base.sail:31161.35-31161.36"
  let slices := (Int.ediv SVL esize)
  sail_assert ((slice_name ≥b 0) && (slice_name <b slices)) "src/v8_base.sail:31163.48-31163.49"
  (ZAvector_read (tile +i (slice_name *i tiles)) width)

/-- Type quantifiers: esize : Int, slice_name : Int, tile : Int, width : Nat, width ≥ 0 -/
def ZAhslice_set (tile : Int) (esize : Int) (slice_name : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let SVL ← do (CurrentSVL_read ())
  sail_assert ((esize == 8) || ((esize == 16) || ((esize == 32) || ((esize == 64) || (esize == 128))))) "src/v8_base.sail:31173.78-31173.79"
  let tiles := (Int.ediv esize 8)
  sail_assert ((tile ≥b 0) && (tile <b tiles)) "src/v8_base.sail:31175.35-31175.36"
  let slices := (Int.ediv SVL esize)
  sail_assert ((slice_name ≥b 0) && (slice_name <b slices)) "src/v8_base.sail:31177.48-31177.49"
  (ZAvector_set (tile +i (slice_name *i tiles)) width value_name)

def GCSSS1 (incoming_pointer_name : (BitVec 64)) : SailM Unit := do
  if ((! (← (GCSEnabled (← readReg PSTATE).EL))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  let accdesc ← (( do (CreateAccDescGCSSS1 (← readReg PSTATE).EL) ) : SailM AccessDescriptor )
  let outgoing_pointer ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let cmpoperand : (BitVec 64) := ((Sail.BitVec.extractLsb incoming_pointer_name 63 12) +++ 0b000000000001#12)
  let operand : (BitVec 64) := ((Sail.BitVec.extractLsb outgoing_pointer 63 3) +++ 0b101#3)
  let data ← (( do (MemAtomic incoming_pointer_name cmpoperand operand accdesc) ) : SailM (BitVec 64) )
  if ((data == cmpoperand) : Bool)
  then (SetCurrentGCSPointer ((Sail.BitVec.extractLsb incoming_pointer_name 63 3) +++ 0b000#3))
  else (GCSDataCheckException GCSInstType_SS1)

def GCSSS2 (_ : Unit) : SailM (BitVec 64) := do
  let outgoing_pointer ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let accdesc_ld ← (( do (CreateAccDescGCS (← readReg PSTATE).EL MemOp_LOAD) ) : SailM AccessDescriptor )
  let accdesc_st ← (( do (CreateAccDescGCS (← readReg PSTATE).EL MemOp_STORE) ) : SailM AccessDescriptor )
  if ((! (← (GCSEnabled (← readReg PSTATE).EL))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  let incoming_pointer_name ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let outgoing_value ← (( do (Mem_read incoming_pointer_name 8 accdesc_ld) ) : SailM (BitVec 64) )
  if (((Sail.BitVec.extractLsb outgoing_value 2 0) == 0b101#3) : Bool)
  then
    (do
      let outgoing_pointer : (BitVec 64) := (Sail.BitVec.updateSubrange outgoing_pointer 63 3 (BitVec.subInt (Sail.BitVec.extractLsb outgoing_value 63 3) 1))
      let outgoing_pointer : (BitVec 64) := (Sail.BitVec.updateSubrange outgoing_pointer 2 0 0b000#3)
      let outgoing_value : (BitVec 64) := ((Sail.BitVec.extractLsb outgoing_pointer 63 12) +++ 0b000000000001#12)
      (Mem_set outgoing_pointer 8 accdesc_st outgoing_value)
      (SetCurrentGCSPointer (BitVec.addInt incoming_pointer_name 8))
      let _ : Unit := (GCSSynchronizationBarrier ())
      (pure outgoing_pointer))
  else
    (do
      (GCSDataCheckException GCSInstType_SS2)
      (pure outgoing_pointer))

def _set_HFGITR_EL2_Type_ATS1E0R (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E0R r v)

def _set_HFGITR_EL2_Type_ATS1E0W (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E0W r v)

def _set_HFGITR_EL2_Type_ATS1E1R (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E1R r v)

def _set_HFGITR_EL2_Type_ATS1E1RP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E1RP r v)

def _set_HFGITR_EL2_Type_ATS1E1W (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E1W r v)

def _set_HFGITR_EL2_Type_ATS1E1WP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ATS1E1WP r v)

def _set_HFGITR_EL2_Type_CFPRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_CFPRCTX r v)

def _set_HFGITR_EL2_Type_COSPRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_COSPRCTX r v)

def _set_HFGITR_EL2_Type_CPPRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_CPPRCTX r v)

def _set_HFGITR_EL2_Type_DCCISW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCISW r v)

def _set_HFGITR_EL2_Type_DCCIVAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCIVAC r v)

def _set_HFGITR_EL2_Type_DCCSW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCSW r v)

def _set_HFGITR_EL2_Type_DCCVAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCVAC r v)

def _set_HFGITR_EL2_Type_DCCVADP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCVADP r v)

def _set_HFGITR_EL2_Type_DCCVAP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCVAP r v)

def _set_HFGITR_EL2_Type_DCCVAU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCCVAU r v)

def _set_HFGITR_EL2_Type_DCISW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCISW r v)

def _set_HFGITR_EL2_Type_DCIVAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCIVAC r v)

def _set_HFGITR_EL2_Type_DCZVA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DCZVA r v)

def _set_HFGITR_EL2_Type_DVPRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_DVPRCTX r v)

def _set_HFGITR_EL2_Type_ERET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ERET r v)

def _set_HFGITR_EL2_Type_ICIALLU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ICIALLU r v)

def _set_HFGITR_EL2_Type_ICIALLUIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ICIALLUIS r v)

def _set_HFGITR_EL2_Type_ICIVAU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_ICIVAU r v)

def _set_HFGITR_EL2_Type_SVC_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_SVC_EL0 r v)

def _set_HFGITR_EL2_Type_SVC_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_SVC_EL1 r v)

def _set_HFGITR_EL2_Type_TLBIASIDE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIASIDE1 r v)

def _set_HFGITR_EL2_Type_TLBIASIDE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIASIDE1IS r v)

def _set_HFGITR_EL2_Type_TLBIASIDE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIASIDE1OS r v)

def _set_HFGITR_EL2_Type_TLBIRVAAE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAAE1 r v)

def _set_HFGITR_EL2_Type_TLBIRVAAE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAAE1IS r v)

def _set_HFGITR_EL2_Type_TLBIRVAAE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAAE1OS r v)

def _set_HFGITR_EL2_Type_TLBIRVAALE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAALE1 r v)

def _set_HFGITR_EL2_Type_TLBIRVAALE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAALE1IS r v)

def _set_HFGITR_EL2_Type_TLBIRVAALE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAALE1OS r v)

def _set_HFGITR_EL2_Type_TLBIRVAE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAE1 r v)

def _set_HFGITR_EL2_Type_TLBIRVAE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAE1IS r v)

def _set_HFGITR_EL2_Type_TLBIRVAE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVAE1OS r v)

def _set_HFGITR_EL2_Type_TLBIRVALE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVALE1 r v)

def _set_HFGITR_EL2_Type_TLBIRVALE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVALE1IS r v)

def _set_HFGITR_EL2_Type_TLBIRVALE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIRVALE1OS r v)

def _set_HFGITR_EL2_Type_TLBIVAAE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAAE1 r v)

def _set_HFGITR_EL2_Type_TLBIVAAE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAAE1IS r v)

def _set_HFGITR_EL2_Type_TLBIVAAE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAAE1OS r v)

def _set_HFGITR_EL2_Type_TLBIVAALE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAALE1 r v)

def _set_HFGITR_EL2_Type_TLBIVAALE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAALE1IS r v)

def _set_HFGITR_EL2_Type_TLBIVAALE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAALE1OS r v)

def _set_HFGITR_EL2_Type_TLBIVAE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAE1 r v)

def _set_HFGITR_EL2_Type_TLBIVAE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAE1IS r v)

def _set_HFGITR_EL2_Type_TLBIVAE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVAE1OS r v)

def _set_HFGITR_EL2_Type_TLBIVALE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVALE1 r v)

def _set_HFGITR_EL2_Type_TLBIVALE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVALE1IS r v)

def _set_HFGITR_EL2_Type_TLBIVALE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVALE1OS r v)

def _set_HFGITR_EL2_Type_TLBIVMALLE1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVMALLE1 r v)

def _set_HFGITR_EL2_Type_TLBIVMALLE1IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVMALLE1IS r v)

def _set_HFGITR_EL2_Type_TLBIVMALLE1OS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_TLBIVMALLE1OS r v)

def _set_HFGITR_EL2_Type_nBRBIALL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_nBRBIALL r v)

def _set_HFGITR_EL2_Type_nBRBINJ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_nBRBINJ r v)

def _set_HFGITR_EL2_Type_nGCSEPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_nGCSEPP r v)

def _set_HFGITR_EL2_Type_nGCSPUSHM_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_nGCSPUSHM_EL1 r v)

def _set_HFGITR_EL2_Type_nGCSSTR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGITR_EL2_Type_nGCSSTR_EL1 r v)

def CheckGCSSTREnabled (_ : Unit) : SailM Unit := do
  let questionMark ← do (pure (← readReg PSTATE).EL)
  if ((questionMark == EL0) : Bool)
  then
    (do
      if (((_get_GCSCRE0_EL1_Type_STREn (← readReg GCSCRE0_EL1)) == 0#1) : Bool)
      then
        (do
          if (((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1) : Bool)
          then (GCSSTRTrapException EL1)
          else (GCSSTRTrapException EL2))
      else (pure ()))
  else
    (do
      if ((questionMark == EL1) : Bool)
      then
        (do
          if (((_get_GCSCR_EL1_Type_STREn (← readReg GCSCR_EL1)) == 0#1) : Bool)
          then (GCSSTRTrapException EL1)
          else
            (do
              if ((←((EL2Enabled ()) <&&> (do
                   (pure (! (HaveEL EL3))) <||> (do
                     (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do
                   (pure ((_get_HFGITR_EL2_Type_nGCSSTR_EL1 (← readReg HFGITR_EL2)) == 0#1))))) : Bool)
              then (GCSSTRTrapException EL2)
              else (pure ())))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              if (((_get_GCSCR_EL2_Type_STREn (← readReg GCSCR_EL2)) == 0#1) : Bool)
              then (GCSSTRTrapException EL2)
              else (pure ()))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  if (((_get_GCSCR_EL3_Type_STREn (← readReg GCSCR_EL3)) == 0#1) : Bool)
                  then (GCSSTRTrapException EL3)
                  else (pure ()))
              else (pure ()))))

def CheckMOPSEnabled (_ : Unit) : SailM Unit := do
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
       (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
       (EL2Enabled ())) <&&> (do
       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1)) <||> (do
         (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1)))) <&&> (do
       (pure (! (← (IsHCRXEL2Enabled ())))) <||> (do
         (pure ((_get_HCRX_EL2_Type_MSCEn (← readReg HCRX_EL2)) == 0#1)))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <&&> (do
       (pure ((_get_SCTLR_EL1_Type_MSCEn (← readReg SCTLR_EL1)) == 0#1))) <&&> (do
       (pure (! (← (EL2Enabled ())))) <||> (do
         (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1))) <||> (do
         (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1)))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <&&> (do
       (IsInHost ())) <&&> (do
       (pure ((_get_SCTLR_EL2_Type_MSCEn (← readReg SCTLR_EL2)) == 0#1))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())

def MismatchedCpySetTargetEL (_ : Unit) : SailM (BitVec 2) := do
  let target_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  if (((BitVec.toNat (← readReg PSTATE).EL) >b (BitVec.toNat EL1)) : Bool)
  then (do (pure (← readReg PSTATE).EL))
  else
    (do
      if ((←((pure ((← readReg PSTATE).EL == EL0)) <&&> (do
           (EL2Enabled ())) <&&> (do
           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
      then (pure EL2)
      else
        (do
          if ((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
               (EL2Enabled ())) <&&> (do
               (IsHCRXEL2Enabled ())) <&&> (do
               (pure ((_get_HCRX_EL2_Type_MCE2 (← readReg HCRX_EL2)) == 1#1))))) : Bool)
          then (pure EL2)
          else (pure EL1)))

/-- Type quantifiers: N : Nat, N = 32 -/
def BFRound (op : real) (N : Nat) : SailM (BitVec N) := do
  sail_assert (N == 32) "src/v8_base.sail:32006.18-32006.19"
  sail_assert (bne op (0)) "src/v8_base.sail:32007.20-32007.21"
  let result ← (( do (undefined_bitvector N) ) : SailM (BitVec N) )
  let minimum_exp := (Neg.neg 126)
  let E := 8
  let F := 23
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let mantissa ← (( do (undefined_real ()) ) : SailM real )
  let (mantissa, sign) : (real × (BitVec 1)) :=
    if ((lt_real op (0)) : Bool)
    then
      (let sign : (BitVec 1) := 1#1
      let mantissa : real := (neg_real op)
      (mantissa, sign))
    else
      (let sign : (BitVec 1) := 0#1
      let mantissa : real := op
      (mantissa, sign))
  let exponent : Int := 0
  let (exponent, mantissa) ← (( do
    let mut loop_vars := (exponent, mantissa)
    while (λ (exponent, mantissa) => (lt_real mantissa (1))) loop_vars do
      let (exponent, mantissa) := loop_vars
      loop_vars :=
        (let mantissa : real := (mult_real mantissa (2))
        let exponent : Int := (exponent -i 1)
        (exponent, mantissa) : (Int × real))
    (pure loop_vars) ) : SailM (Int × real) )
  let (exponent, mantissa) ← (( do
    let mut loop_vars_1 := (exponent, mantissa)
    while (λ (exponent, mantissa) => (gteq_real mantissa (2))) loop_vars_1 do
      let (exponent, mantissa) := loop_vars_1
      loop_vars_1 :=
        (let mantissa : real := (div_real mantissa (2))
        let exponent : Int := (exponent +i 1)
        (exponent, mantissa) : (Int × real))
    (pure loop_vars_1) ) : SailM (Int × real) )
  let exponent := exponent
  if ((exponent <b minimum_exp) : Bool)
  then (FPZero sign N)
  else
    (do
      let biased_exp := (Max.max ((exponent -i minimum_exp) +i 1) 0)
      let mantissa := mantissa
      let int_mant : Int := (round_down (mult_real mantissa (real_power (2) F)))
      let error : real := (sub_real (mult_real mantissa (real_power (2) F)) (to_real int_mant))
      let int_mant : Int :=
        if ((bne error (0)) : Bool)
        then (integer_update_subrange int_mant 0 0 1#1)
        else int_mant
      let int_mant := int_mant
      if ((biased_exp ≥b ((2 ^i E) -i 1)) : Bool)
      then (do (FPInfinity sign N))
      else (pure ((sign +++ (integer_subrange biased_exp ((N -i 2) -i F) 0)) +++ (integer_subrange int_mant (F -i 1) 0))))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32] -/
def BFUnpack (fpval : (BitVec k_N)) : SailM (FPType × (BitVec 1) × real) := do
  sail_assert (((Sail.BitVec.length fpval) == 16) || ((Sail.BitVec.length fpval) == 32)) "src/v8_base.sail:32056.30-32056.31"
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let exp ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
  let frac ← (( do (undefined_bitvector 23) ) : SailM (BitVec 23) )
  let (exp, frac, sign) : ((BitVec 8) × (BitVec 23) × (BitVec 1)) :=
    if (((Sail.BitVec.length fpval) == 16) : Bool)
    then
      (let sign : (BitVec 1) := (BitVec.join1 [(BitVec.access fpval 15)])
      let exp : (BitVec 8) := (Sail.BitVec.extractLsb fpval 14 7)
      let frac : (BitVec 23) := ((Sail.BitVec.extractLsb fpval 6 0) +++ (Zeros (n := 16)))
      (exp, frac, sign))
    else
      (let sign : (BitVec 1) := (BitVec.join1 [(BitVec.access fpval 31)])
      let exp : (BitVec 8) := (Sail.BitVec.extractLsb fpval 30 23)
      let frac : (BitVec 23) := (Sail.BitVec.extractLsb fpval 22 0)
      (exp, frac, sign))
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  let (fptype, value_name) : (FPType × real) :=
    if ((IsZero exp) : Bool)
    then
      (let fptype : FPType := FPType_Zero
      let value_name : real := (0)
      (fptype, value_name))
    else
      (let (fptype, value_name) : (FPType × real) :=
        if ((IsOnes exp) : Bool)
        then
          (let (fptype, value_name) : (FPType × real) :=
            if ((IsZero frac) : Bool)
            then
              (let fptype : FPType := FPType_Infinity
              let value_name : real := (real_power (2) 1000000)
              (fptype, value_name))
            else
              (let fptype : FPType := FPType_QNaN
              let value_name : real := (0)
              (fptype, value_name))
          (fptype, value_name))
        else
          (let fptype : FPType := FPType_Nonzero
          let value_name : real := (mult_real (real_power (2) ((BitVec.toNat exp) -i 127)) (add_real (1) (mult_real (to_real (BitVec.toNat frac)) (real_power (2) (Neg.neg 23)))))
          (fptype, value_name))
      (fptype, value_name))
  let value_name : real :=
    if ((sign == 1#1) : Bool)
    then (neg_real value_name)
    else value_name
  let value_name := value_name
  (pure (fptype, sign, value_name))

def AArch64_PhysicalSErrorTarget (_ : Unit) : SailM (Bool × (BitVec 2)) := do
  let route_to_el3 ← (( do (undefined_bool ()) ) : SailM Bool )
  let route_to_el2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let route_to_el3 ← (( do
    if (((← readReg PSTATE).EL != EL3) : Bool)
    then (do (pure (HaveEL EL3)) <&&> (do (pure ((← (EffectiveEA ())) == 1#1))))
    else (pure false) ) : SailM Bool )
  let route_to_el2 ← (( do
    if ((←((pure (! route_to_el3)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure ((← readReg PSTATE).EL == EL1))))) : Bool)
    then (do (pure ((_get_HCR_EL2_Type_AMO (← readReg HCR_EL2)) == 1#1)))
    else
      (do
        if ((←((pure (! route_to_el3)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure ((← readReg PSTATE).EL == EL0))))) : Bool)
        then (do (pure (! (← (IsInHost ())))) <&&> (do (pure (((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_AMO (← readReg HCR_EL2))) != 0b00#2))))
        else (pure false)) ) : SailM Bool )
  let masked ← (( do (undefined_bool ()) ) : SailM Bool )
  let masked ← (( do
    let questionMark ← do (pure (← readReg PSTATE).EL)
    if ((questionMark == EL3) : Bool)
    then (do (pure ((← (EffectiveEA ())) == 0#1)) <||> (do (pure ((← readReg PSTATE).A == 1#1))))
    else
      (do
        if ((questionMark == EL2) : Bool)
        then (do (pure (! route_to_el3)) <&&> (do (pure (((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_AMO (← readReg HCR_EL2))) == 0b00#2)) <||> (do (pure ((← readReg PSTATE).A == 1#1)))))
        else
          (do
            if ((questionMark == EL1) : Bool)
            then (do (pure ((! route_to_el3) && (! route_to_el2))) <&&> (do (pure ((← readReg PSTATE).A == 1#1))))
            else
              (do
                if ((questionMark == EL0) : Bool)
                then (do (pure ((! route_to_el3) && (! route_to_el2))) <&&> (do (pure ((← readReg PSTATE).A == 1#1))))
                else (pure masked)))) ) : SailM Bool )
  let masked ← (( do
    if ((← (HaveDoubleFault2Ext ())) : Bool)
    then
      (do
        let nmea_bit ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
        let nmea_bit ← (( do
          let questionMark ← do (pure (← readReg PSTATE).EL)
          if ((questionMark == EL3) : Bool)
          then (do (pure (_get_SCR_EL3_Type_NMEA (← readReg SCR_EL3))))
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  if ((← (IsSCTLR2EL2Enabled ())) : Bool)
                  then (pure (_get_SCTLR2_EL2_Type_NMEA (← readReg SCTLR2_EL2)))
                  else (pure 0#1))
              else
                (do
                  if ((questionMark == EL1) : Bool)
                  then
                    (do
                      if ((← (IsSCTLR2EL1Enabled ())) : Bool)
                      then (pure (_get_SCTLR2_EL1_Type_NMEA (← readReg SCTLR2_EL1)))
                      else (pure 0#1))
                  else
                    (do
                      if ((questionMark == EL0) : Bool)
                      then
                        (do
                          if ((← (IsInHost ())) : Bool)
                          then
                            (do
                              if ((← (IsSCTLR2EL2Enabled ())) : Bool)
                              then (pure (_get_SCTLR2_EL2_Type_NMEA (← readReg SCTLR2_EL2)))
                              else (pure 0#1))
                          else
                            (do
                              if ((← (IsSCTLR2EL1Enabled ())) : Bool)
                              then (pure (_get_SCTLR2_EL1_Type_NMEA (← readReg SCTLR2_EL1)))
                              else (pure 0#1)))
                      else (pure nmea_bit)))) ) : SailM (BitVec 1) )
        (pure (masked && (nmea_bit == 0#1))))
    else
      (do
        if ((←((HaveDoubleFaultExt ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL3))))) : Bool)
        then
          (do
            let nmea_bit ← (( do (pure ((_get_SCR_EL3_Type_NMEA (← readReg SCR_EL3)) &&& (← (EffectiveEA ())))) ) : SailM (BitVec 1) )
            (pure (masked && (nmea_bit == 0#1))))
        else (pure masked)) ) : SailM Bool )
  let route_masked_to_el3 ← (( do (undefined_bool ()) ) : SailM Bool )
  let route_masked_to_el2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let (route_masked_to_el2, route_masked_to_el3) ← (( do
    if ((← (HaveDoubleFault2Ext ())) : Bool)
    then
      (do
        let route_masked_to_el2 ← (pure ((← (EL2Enabled ())) && (! route_to_el3))) <&&> (do (IsHCRXEL2Enabled ())) <&&> (do (pure ((_get_HCRX_EL2_Type_TMEA (← readReg HCRX_EL2)) == 1#1))) <&&> (do (pure ((← readReg PSTATE).EL == EL1)) <&&> (do (pure (((← readReg PSTATE).A == 1#1) || masked))) <||> (do (pure (((← readReg PSTATE).EL == EL0) && masked)) <&&> (do (pure (! (← (IsInHost ())))))))
        let route_masked_to_el3 ← (pure ((←((pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_TMEA (← readReg SCR_EL3)) == 1#1))))) && (! (route_to_el2 || route_masked_to_el2)))) <&&> (do (pure ((← readReg PSTATE).EL == EL2)) <||> (do (pure ((← readReg PSTATE).EL == EL1))) <&&> (do (pure (((← readReg PSTATE).A == 1#1) || masked))) <||> (do (pure (((← readReg PSTATE).EL == EL0) && masked))))
        (pure (route_masked_to_el2, route_masked_to_el3)))
    else
      (let route_masked_to_el2 : Bool := false
      let route_masked_to_el3 : Bool := false
      (pure (route_masked_to_el2, route_masked_to_el3))) ) : SailM (Bool × Bool) )
  let take_in_el3 ← (( do (pure (((← readReg PSTATE).EL == EL3) && (! masked))) ) : SailM Bool )
  let take_in_el2_0 ← (( do (pure (((←((pure ((← readReg PSTATE).EL == EL2)) <||> (do (IsInHost ())))) && (! (route_to_el3 || route_masked_to_el3))) && (! masked))) ) : SailM Bool )
  let take_in_el1_0 ← (( do (pure ((((←((pure ((← readReg PSTATE).EL == EL1)) <||> (do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (pure (! (← (IsInHost ())))))))) && (! (route_to_el2 || route_masked_to_el2))) && (! (route_to_el3 || route_masked_to_el3))) && (! masked))) ) : SailM Bool )
  let target_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let (masked, target_el) ← (( do
    if (((take_in_el3 || route_to_el3) || route_masked_to_el3) : Bool)
    then
      (let masked : Bool := false
      let target_el : (BitVec 2) := EL3
      (pure (masked, target_el)))
    else
      (do
        let (masked, target_el) ← (( do
          if (((take_in_el2_0 || route_to_el2) || route_masked_to_el2) : Bool)
          then
            (let masked : Bool := false
            let target_el : (BitVec 2) := EL2
            (pure (masked, target_el)))
          else
            (do
              let (masked, target_el) ← (( do
                if (take_in_el1_0 : Bool)
                then
                  (let masked : Bool := false
                  let target_el : (BitVec 2) := EL1
                  (pure (masked, target_el)))
                else
                  (do
                    let masked : Bool := true
                    let target_el ← (__UNKNOWN_bits 2)
                    (pure (masked, target_el))) ) : SailM (Bool × (BitVec 2)) )
              (pure (masked, target_el))) ) : SailM (Bool × (BitVec 2)) )
        (pure (masked, target_el))) ) : SailM (Bool × (BitVec 2)) )
  (pure (masked, target_el))

def _set_DISR_EL1_Type_DFSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_EL1_Type_DFSC r v)

def _set_DISR_Type_DFSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_Type_DFSC r v)

def _set_DISR_EL1_Type_IDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DISR_EL1_Type_IDS r v)

def _set_ID_AA64MMFR2_EL1_Type_IDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_IDS r v)

def _set_VDISR_EL2_Type_IDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VDISR_EL2_Type_IDS r v)

def _set_VSESR_EL2_Type_IDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VSESR_EL2_Type_IDS r v)

def AArch64_vESBOperation (_ : Unit) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
    (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
    (EL2Enabled ())))) "src/v8_base.sail:33362.63-33362.64"
  let vSEI_enabled ← (( do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1)) <&&> (do (pure ((_get_HCR_EL2_Type_AMO (← readReg HCR_EL2)) == 1#1))) ) : SailM Bool )
  let vSEI_pending ← (( do (pure vSEI_enabled) <&&> (do (pure ((_get_HCR_EL2_Type_VSE (← readReg HCR_EL2)) == 1#1))) ) : SailM Bool )
  let vintdis ← (( do (Halted ()) <||> (do (ExternalDebugInterruptsDisabled EL1)) ) : SailM Bool )
  let vmasked ← (( do (pure vintdis) <||> (do (pure ((← readReg PSTATE).A == 1#1))) ) : SailM Bool )
  if ((vSEI_pending && vmasked) : Bool)
  then
    (do
      if ((← (ELUsingAArch32 EL1)) : Bool)
      then
        (do
          let target : (BitVec 32) := (Zeros (n := 32))
          let target : (BitVec 32) := (BitVec.update target 31 (Bit 1#1))
          let target ← (pure (Sail.BitVec.updateSubrange target 15 14 (Sail.BitVec.extractLsb (← (VDFSR_read ())) 15 14)))
          let target ← (pure (BitVec.update target 12 (Bit (BitVec.join1 [(BitVec.access (← (VDFSR_read ())) 12)]))))
          let target ← (pure (BitVec.update target 9 (Bit (_get_TTBCR_Type_EAE (← (TTBCR_read ()))))))
          let target ← (( do
            if (((_get_TTBCR_Type_EAE (← (TTBCR_read ()))) == 1#1) : Bool)
            then (pure (Sail.BitVec.updateSubrange target 5 0 0b010001#6))
            else
              (let target : (BitVec 32) := (Sail.BitVec.updateSubrange target 10 10 (Sail.BitVec.extractLsb 0b10110#5 4 4))
              (pure (Sail.BitVec.updateSubrange target 3 0 (Sail.BitVec.extractLsb 0b10110#5 3 0)))) ) : SailM (BitVec 32) )
          (VDISR_write (Mk_VDISR_Type target)))
      else
        (do
          let target : (BitVec 64) := (Zeros (n := 64))
          let target : (BitVec 64) := (BitVec.update target 31 (Bit 1#1))
          let target ← (pure (Sail.BitVec.updateSubrange target 24 0 (Sail.BitVec.extractLsb (← readReg VSESR_EL2) 24 0)))
          writeReg VDISR_EL2 (Mk_VDISR_EL2_Type target))
      writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 8 8 0#1))
  else (pure ())

/-- Type quantifiers: pl : Int, vl : Int -/
def TakeTransactionCheckpoint (vl : Int) (pl : Int) : SailM Unit := do
  writeReg TSTATE { (← readReg TSTATE) with SP := ← (do (SP_read ())) }
  writeReg TSTATE { (← readReg TSTATE) with ICC_PMR_EL1 := ← (do readReg ICC_PMR_EL1) }
  writeReg TSTATE { (← readReg TSTATE) with nzcv := ← (do (pure ((← readReg PSTATE).N +++ ((← readReg PSTATE).Z +++ ((← readReg PSTATE).C +++ (← readReg PSTATE).V))))) }
  let split_vec ← do (pure ((← readReg PSTATE).D +++ ((← readReg PSTATE).A +++ ((← readReg PSTATE).I +++ (← readReg PSTATE).F))))
  writeReg TSTATE { (← readReg TSTATE) with D := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg TSTATE { (← readReg TSTATE) with A := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg TSTATE { (← readReg TSTATE) with I := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg TSTATE { (← readReg TSTATE) with F := (Sail.BitVec.extractLsb split_vec 0 0) }
  let loop_n_lower := 0
  let loop_n_upper := 30
  let mut loop_vars := ()
  for n in [loop_n_lower:loop_n_upper:1]i do
    let () := loop_vars
    loop_vars ← do writeReg TSTATE { (← readReg TSTATE) with X := ← (do (pure (vectorUpdate (← readReg TSTATE).X n (← (X_read n 64))))) }
  (pure loop_vars)
  if ((← (IsFPEnabled (← readReg PSTATE).EL)) : Bool)
  then
    (do
      if ((← (IsSVEEnabled (← readReg PSTATE).EL)) : Bool)
      then
        (do
          let loop_n_lower := 0
          let loop_n_upper := 31
          let mut loop_vars_2 := ()
          for n in [loop_n_lower:loop_n_upper:1]i do
            let () := loop_vars_2
            loop_vars_2 ← do
              sail_assert ((0 ≤b (vl -i 1)) && ((vl -i 1) <b 2048)) "src/v8_base.sail:33408.66-33408.67"
              writeReg TSTATE { (← readReg TSTATE) with Z := ← (do (pure (vectorUpdate (← readReg TSTATE).Z n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg TSTATE).Z n) (vl -i 1) 0 (← (Z_read n vl)))))) }
          (pure loop_vars_2)
          let loop_n_lower := 0
          let loop_n_upper := 15
          let mut loop_vars_3 := ()
          for n in [loop_n_lower:loop_n_upper:1]i do
            let () := loop_vars_3
            loop_vars_3 ← do
              sail_assert ((0 ≤b (pl -i 1)) && ((pl -i 1) <b 256)) "src/v8_base.sail:33412.65-33412.66"
              writeReg TSTATE { (← readReg TSTATE) with P := ← (do (pure (vectorUpdate (← readReg TSTATE).P n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg TSTATE).P n) (pl -i 1) 0 (← (P_read n pl)))))) }
          (pure loop_vars_3)
          sail_assert ((0 ≤b (pl -i 1)) && ((pl -i 1) <b 256)) "src/v8_base.sail:33415.61-33415.62"
          writeReg TSTATE { (← readReg TSTATE) with FFR := ← (do (pure (Sail.BitVec.updateSubrange (← readReg TSTATE).FFR (pl -i 1) 0 (← (FFR_read pl))))) })
      else
        (do
          let loop_n_lower := 0
          let loop_n_upper := 31
          let mut loop_vars_1 := ()
          for n in [loop_n_lower:loop_n_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do writeReg TSTATE { (← readReg TSTATE) with Z := ← (do (pure (vectorUpdate (← readReg TSTATE).Z n (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg TSTATE).Z n) 127 0 (← (V_read n 128)))))) }
          (pure loop_vars_1))
      writeReg TSTATE { (← readReg TSTATE) with FPCR := ← (do readReg FPCR) }
      writeReg TSTATE { (← readReg TSTATE) with FPSR := ← (do readReg FPSR) })
  else (pure ())
  if ((← (HaveGCS ())) : Bool)
  then
    (do
      let questionMark ← do (pure (← readReg PSTATE).EL)
      if ((questionMark == EL0) : Bool)
      then writeReg TSTATE { (← readReg TSTATE) with GCSPR_ELx := ← (do readReg GCSPR_EL0) }
      else
        (do
          if ((questionMark == EL1) : Bool)
          then writeReg TSTATE { (← readReg TSTATE) with GCSPR_ELx := ← (do readReg GCSPR_EL1) }
          else
            (do
              if ((questionMark == EL2) : Bool)
              then writeReg TSTATE { (← readReg TSTATE) with GCSPR_ELx := ← (do readReg GCSPR_EL2) }
              else
                (do
                  if ((questionMark == EL3) : Bool)
                  then writeReg TSTATE { (← readReg TSTATE) with GCSPR_ELx := ← (do readReg GCSPR_EL3) }
                  else (pure ())))))
  else (pure ())

def _set_RVBAR_EL1_Type_ResetAddress (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVBAR_EL1_Type_ResetAddress r v)

def _set_RVBAR_EL2_Type_ResetAddress (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVBAR_EL2_Type_ResetAddress r v)

def _set_RVBAR_EL3_Type_ResetAddress (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RVBAR_EL3_Type_ResetAddress r v)

def CSSELR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_CSSELR_Type ()) ) : SailM CSSELR_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg CSSELR_S)
  else (do (CSSELR_NS_read ()))

def CSSELR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CSSELR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg CSSELR_S r
  else (CSSELR_NS_write r)

def DFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_DFSR_Type ()) ) : SailM DFSR_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg DFSR_S)
  else (do (DFSR_NS_read ()))

def ICC_BPR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_BPR1_Type ()) ) : SailM ICC_BPR1_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do (ICC_BPR1_S_read ()))
  else (do (ICC_BPR1_NS_read ()))

def ICC_BPR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_BPR1_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (ICC_BPR1_S_write r)
  else (ICC_BPR1_NS_write r)

def ICC_CTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_CTLR_Type ()) ) : SailM ICC_CTLR_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do (ICC_CTLR_S_read ()))
  else (do (ICC_CTLR_NS_read ()))

def ICC_CTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_CTLR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (ICC_CTLR_S_write r)
  else (ICC_CTLR_NS_write r)

def ICC_IGRPEN1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_IGRPEN1_Type ()) ) : SailM ICC_IGRPEN1_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do (ICC_IGRPEN1_S_read ()))
  else (do (ICC_IGRPEN1_NS_read ()))

def ICC_IGRPEN1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IGRPEN1_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (ICC_IGRPEN1_S_write r)
  else (ICC_IGRPEN1_NS_write r)

def ICC_SRE_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_SRE_Type ()) ) : SailM ICC_SRE_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do (ICC_SRE_S_read ()))
  else (do (ICC_SRE_NS_read ()))

def ICC_SRE_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_SRE_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (ICC_SRE_S_write r)
  else (ICC_SRE_NS_write r)

def IFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_IFSR_Type ()) ) : SailM IFSR_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg IFSR_S)
  else (do (IFSR_NS_read ()))

def PAR_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_PAR_Type ()) ) : SailM PAR_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg PAR_S)
  else (do readReg PAR_NS)

def PRRR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PRRR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg PRRR_S r
  else (PRRR_NS_write r)

def SCTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : SCTLR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg SCTLR_S r
  else (SCTLR_NS_write r)

def SDER_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : SDER_Type := value_name
  if ((HaveEL EL3) : Bool)
  then (SDER32_EL3_write (Mk_SDER32_EL3_Type (set_slice 32 (← (SDER32_EL3_read ())) 0 (BitVec.slice r 0 32))))
  else writeReg SDER32_EL2 (Sail.BitVec.updateSubrange (← readReg SDER32_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _SDER r

def TTBCR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TTBCR2_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg TTBCR2_S r
  else (TTBCR2_NS_write r)

def TTBCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TTBCR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg TTBCR_S r
  else (TTBCR_NS_write r)

def VBAR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VBAR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg VBAR_S r
  else (VBAR_NS_write r)

def NMRR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : NMRR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg NMRR_S r
  else (NMRR_NS_write r)

def ICC_BPR1_EL1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_BPR1_EL1_Type ()) ) : SailM ICC_BPR1_EL1_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg ICC_BPR1_EL1_S)
  else (do readReg ICC_BPR1_EL1_NS)

def ICC_CTLR_EL1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_CTLR_EL1_Type ()) ) : SailM ICC_CTLR_EL1_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg ICC_CTLR_EL1_S)
  else (do readReg ICC_CTLR_EL1_NS)

def ICC_IGRPEN1_EL1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_IGRPEN1_EL1_Type ()) ) : SailM ICC_IGRPEN1_EL1_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg ICC_IGRPEN1_EL1_S)
  else (do readReg ICC_IGRPEN1_EL1_NS)

def ICC_SRE_EL1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_SRE_EL1_Type ()) ) : SailM ICC_SRE_EL1_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg ICC_SRE_EL1_S)
  else (do readReg ICC_SRE_EL1_NS)

def MPAM1_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM1_EL1_Type := value_name
  if ((HaveEL EL3) : Bool)
  then (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 1 (← (MPAM3_EL3_read ())) 63 (BitVec.slice r 63 1))))
  else writeReg MPAM2_EL2 (BitVec.update (← readReg MPAM2_EL2) 63 (Bit (BitVec.slice r 63 1)))
  writeReg _MPAM1_EL1 r

def TTBR0_EL1_write (value_name : (BitVec 128)) : SailM Unit := do
  let r : TTBR0_EL1_Type := value_name
  (TTBR0_write (Mk_TTBR0_Type (set_slice 64 (← (TTBR0_read ())) 0 (BitVec.slice r 0 64))))
  writeReg _TTBR0_EL1 r

def TTBR1_EL1_write (value_name : (BitVec 128)) : SailM Unit := do
  let r : TTBR1_EL1_Type := value_name
  (TTBR1_write (Mk_TTBR1_Type (set_slice 64 (← (TTBR1_read ())) 0 (BitVec.slice r 0 64))))
  writeReg _TTBR1_EL1 r

def AArch64_CallSecureMonitor (immediate : (BitVec 16)) : SailM Unit := do
  sail_assert (←((pure (HaveEL EL3)) <&&> (do
    (pure (! (← (ELUsingAArch32 EL3))))))) "src/v8_base.sail:33567.54-33567.55"
  if ((← (UsingAArch32 ())) : Bool)
  then (AArch32_ITAdvance ())
  else (pure ())
  (SSAdvance ())
  let preferred_exception_return ← (( do (NextInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_MonitorCall) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
  (AArch64_TakeException EL3 except preferred_exception_return vect_offset)

def AArch64_CallHypervisor (immediate : (BitVec 16)) : SailM Unit := do
  sail_assert (HaveEL EL2) "src/v8_base.sail:33582.22-33582.23"
  if ((← (UsingAArch32 ())) : Bool)
  then (AArch32_ITAdvance ())
  else (pure ())
  (SSAdvance ())
  let preferred_exception_return ← (( do (NextInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_HypervisorCall) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
  if (((← readReg PSTATE).EL == EL3) : Bool)
  then (AArch64_TakeException EL3 except preferred_exception_return vect_offset)
  else (AArch64_TakeException EL2 except preferred_exception_return vect_offset)

def AArch64_CallSupervisor (immediate_in : (BitVec 16)) : SailM Unit := do
  let immediate : (BitVec 16) := immediate_in
  if ((← (UsingAArch32 ())) : Bool)
  then (AArch32_ITAdvance ())
  else (pure ())
  (SSAdvance ())
  let route_to_el2 ← (( do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))) ) : SailM Bool )
  let preferred_exception_return ← (( do (NextInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_SupervisorCall) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
  if (((BitVec.toNat (← readReg PSTATE).EL) >b (BitVec.toNat EL1)) : Bool)
  then (AArch64_TakeException (← readReg PSTATE).EL except preferred_exception_return vect_offset)
  else
    (do
      if (route_to_el2 : Bool)
      then (AArch64_TakeException EL2 except preferred_exception_return vect_offset)
      else (AArch64_TakeException EL1 except preferred_exception_return vect_offset))

def CheckLDST64BEnabled (_ : Unit) : SailM Unit := do
  let trap : Bool := false
  let iss : (BitVec 25) := (Sail.BitVec.zeroExtend 0b10#2 25)
  let target_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let (target_el, trap) ← (( do
    if (((← readReg PSTATE).EL == EL0) : Bool)
    then
      (do
        let (target_el, trap) ← (( do
          if ((! (← (IsInHost ()))) : Bool)
          then
            (do
              let trap ← (pure ((_get_SCTLR_EL1_Type_EnALS (← readReg SCTLR_EL1)) == 0#1))
              let target_el ←
                if ((←((EL2Enabled ()) <&&> (do
                     (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                then (pure EL2)
                else (pure EL1)
              (pure (target_el, trap)))
          else
            (do
              let trap ← (pure ((_get_SCTLR_EL2_Type_EnALS (← readReg SCTLR_EL2)) == 0#1))
              let target_el : (BitVec 2) := EL2
              (pure (target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
        (pure (target_el, trap)))
    else
      (let target_el : (BitVec 2) := EL1
      (pure (target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
  let (target_el, trap) ← (( do
    if ((←((pure (! trap)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure ((← readReg PSTATE).EL == EL0)) <&&> (do
           (pure (! (← (IsInHost ()))))) <||> (do
           (pure ((← readReg PSTATE).EL == EL1)))))) : Bool)
    then
      (do
        let trap ← (pure (! (← (IsHCRXEL2Enabled ())))) <||> (do (pure ((_get_HCRX_EL2_Type_EnALS (← readReg HCRX_EL2)) == 0#1)))
        let target_el : (BitVec 2) := EL2
        (pure (target_el, trap)))
    else (pure (target_el, trap)) ) : SailM ((BitVec 2) × Bool) )
  let target_el := target_el
  if (trap : Bool)
  then (LDST64BTrap target_el iss)
  else (pure ())

def CheckST64BVEnabled (_ : Unit) : SailM Unit := do
  let trap : Bool := false
  let iss : (BitVec 25) := (Zeros (n := 25))
  let target_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let (target_el, trap) ← (( do
    if (((← readReg PSTATE).EL == EL0) : Bool)
    then
      (do
        let (target_el, trap) ← (( do
          if ((! (← (IsInHost ()))) : Bool)
          then
            (do
              let trap ← (pure ((_get_SCTLR_EL1_Type_EnASR (← readReg SCTLR_EL1)) == 0#1))
              let target_el ←
                if ((←((EL2Enabled ()) <&&> (do
                     (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                then (pure EL2)
                else (pure EL1)
              (pure (target_el, trap)))
          else
            (do
              let trap ← (pure ((_get_SCTLR_EL2_Type_EnASR (← readReg SCTLR_EL2)) == 0#1))
              let target_el : (BitVec 2) := EL2
              (pure (target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
        (pure (target_el, trap)))
    else (pure (target_el, trap)) ) : SailM ((BitVec 2) × Bool) )
  let (target_el, trap) ← (( do
    if ((←((pure (! trap)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure ((← readReg PSTATE).EL == EL0)) <&&> (do
           (pure (! (← (IsInHost ()))))) <||> (do
           (pure ((← readReg PSTATE).EL == EL1)))))) : Bool)
    then
      (do
        let trap ← (pure (! (← (IsHCRXEL2Enabled ())))) <||> (do (pure ((_get_HCRX_EL2_Type_EnASR (← readReg HCRX_EL2)) == 0#1)))
        let target_el : (BitVec 2) := EL2
        (pure (target_el, trap)))
    else (pure (target_el, trap)) ) : SailM ((BitVec 2) × Bool) )
  let target_el := target_el
  if (trap : Bool)
  then (LDST64BTrap target_el iss)
  else (pure ())

def CheckST64BV0Enabled (_ : Unit) : SailM Unit := do
  let trap : Bool := false
  let iss : (BitVec 25) := (Sail.BitVec.zeroExtend 1#1 25)
  let target_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  if ((←((pure (((← readReg PSTATE).EL != EL3) && (HaveEL EL3))) <&&> (do
       (pure ((_get_SCR_EL3_Type_EnAS0 (← readReg SCR_EL3)) == 0#1))) <&&> (do
       (EL3SDDUndefPriority ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let (target_el, trap) ← (( do
    if (((← readReg PSTATE).EL == EL0) : Bool)
    then
      (do
        let (target_el, trap) ← (( do
          if ((! (← (IsInHost ()))) : Bool)
          then
            (do
              let trap ← (pure ((_get_SCTLR_EL1_Type_EnAS0 (← readReg SCTLR_EL1)) == 0#1))
              let target_el ←
                if ((←((EL2Enabled ()) <&&> (do
                     (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
                then (pure EL2)
                else (pure EL1)
              (pure (target_el, trap)))
          else
            (do
              let trap ← (pure ((_get_SCTLR_EL2_Type_EnAS0 (← readReg SCTLR_EL2)) == 0#1))
              let target_el : (BitVec 2) := EL2
              (pure (target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
        (pure (target_el, trap)))
    else (pure (target_el, trap)) ) : SailM ((BitVec 2) × Bool) )
  let (target_el, trap) ← (( do
    if ((←((pure (! trap)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure ((← readReg PSTATE).EL == EL0)) <&&> (do
           (pure (! (← (IsInHost ()))))) <||> (do
           (pure ((← readReg PSTATE).EL == EL1)))))) : Bool)
    then
      (do
        let trap ← (pure (! (← (IsHCRXEL2Enabled ())))) <||> (do (pure ((_get_HCRX_EL2_Type_EnAS0 (← readReg HCRX_EL2)) == 0#1)))
        let target_el : (BitVec 2) := EL2
        (pure (target_el, trap)))
    else (pure (target_el, trap)) ) : SailM ((BitVec 2) × Bool) )
  let (target_el, trap) ← (( do
    if ((←((pure (! trap)) <&&> (do
         (pure ((← readReg PSTATE).EL != EL3))))) : Bool)
    then
      (do
        let trap ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_EnAS0 (← readReg SCR_EL3)) == 0#1)))
        let target_el : (BitVec 2) := EL3
        (pure (target_el, trap)))
    else (pure (target_el, trap)) ) : SailM ((BitVec 2) × Bool) )
  if (trap : Bool)
  then
    (do
      if ((←((pure (target_el == EL3)) <&&> (do
           (EL3SDDUndef ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (LDST64BTrap target_el iss))
  else (pure ())

/-- Type quantifiers: k_eret_with_pac : Bool, k_pac_uses_key_a : Bool -/
def AArch64_CheckForERetTrap (eret_with_pac : Bool) (pac_uses_key_a : Bool) : SailM Unit := do
  let vect_offset ← (( do (undefined_int ()) ) : SailM Int )
  let route_to_el2 : Bool := false
  let route_to_el2 ← (( do (pure ((← readReg PSTATE).EL == EL1)) <&&> (do (EL2Enabled ())) <&&> (do (HaveNVExt ()) <&&> (do (pure ((_get_HCR_EL2_Type_NV (← readReg HCR_EL2)) == 1#1))) <||> (do (HaveFGTExt ()) <&&> (do (pure (! (HaveEL EL3))) <||> (do (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))) <&&> (do (pure ((_get_HFGITR_EL2_Type_ERET (← readReg HFGITR_EL2)) == 1#1))))) ) : SailM Bool )
  if (route_to_el2 : Bool)
  then
    (do
      let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
      let vect_offset := (BitVec.toNat 0x0#4)
      let except ← (( do (ExceptionSyndrome Exception_ERetTrap) ) : SailM ExceptionRecord )
      let except : ExceptionRecord :=
        if ((! eret_with_pac) : Bool)
        then
          (let except : ExceptionRecord := { except with syndrome := (BitVec.update except.syndrome 1 (Bit 0#1)) }
          { except with syndrome := (BitVec.update except.syndrome 0 (Bit 0#1)) })
        else
          (let except : ExceptionRecord := { except with syndrome := (BitVec.update except.syndrome 1 (Bit 1#1)) }
          if (pac_uses_key_a : Bool)
          then { except with syndrome := (BitVec.update except.syndrome 0 (Bit 0#1)) }
          else { except with syndrome := (BitVec.update except.syndrome 0 (Bit 1#1)) })
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else (pure ())

def AArch64_CheckForSVCTrap (immediate : (BitVec 16)) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  let route_to_el2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let vect_offset ← (( do (undefined_int ()) ) : SailM Int )
  let route_to_el2 ← (( do
    if ((← (HaveFGTExt ())) : Bool)
    then
      (do
        let route_to_el2 : Bool := false
        let route_to_el2 ← (( do
          if (((← readReg PSTATE).EL == EL0) : Bool)
          then (do (pure (! (← (UsingAArch32 ())))) <&&> (do (pure (! (← (ELUsingAArch32 EL1))))) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HFGITR_EL2_Type_SVC_EL0 (← readReg HFGITR_EL2)) == 1#1))) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2)) <&&> (do (pure (! (HaveEL EL3))) <||> (do (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1))))))
          else
            (do
              if (((← readReg PSTATE).EL == EL1) : Bool)
              then (do (EL2Enabled ()) <&&> (do (pure ((_get_HFGITR_EL2_Type_SVC_EL1 (← readReg HFGITR_EL2)) == 1#1))) <&&> (do (pure (! (HaveEL EL3))) <||> (do (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1)))))
              else (pure route_to_el2)) ) : SailM Bool )
        if (route_to_el2 : Bool)
        then
          (do
            let except ← (( do (ExceptionSyndrome Exception_SupervisorCall) ) : SailM ExceptionRecord )
            let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
            let except : ExceptionRecord := { except with trappedsyscallinst := true }
            let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
            let vect_offset := (BitVec.toNat 0x0#4)
            (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
        else (pure ())
        (pure route_to_el2))
    else (pure route_to_el2) ) : SailM Bool )
  let route_to_el2 := route_to_el2
  (pure ())

def _set_HSTR_EL2_Type_T0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T0 r v)

def _set_HSTR_Type_T0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T0 r v)

def _set_HSTR_EL2_Type_T1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T1 r v)

def _set_HSTR_Type_T1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T1 r v)

def _set_HSTR_EL2_Type_T10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T10 r v)

def _set_HSTR_Type_T10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T10 r v)

def _set_HSTR_EL2_Type_T11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T11 r v)

def _set_HSTR_Type_T11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T11 r v)

def _set_HSTR_EL2_Type_T12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T12 r v)

def _set_HSTR_Type_T12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T12 r v)

def _set_HSTR_EL2_Type_T13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T13 r v)

def _set_HSTR_Type_T13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T13 r v)

def _set_HSTR_EL2_Type_T15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T15 r v)

def _set_HSTR_Type_T15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T15 r v)

def _set_HSTR_EL2_Type_T2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T2 r v)

def _set_HSTR_Type_T2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T2 r v)

def _set_HSTR_EL2_Type_T3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T3 r v)

def _set_HSTR_Type_T3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T3 r v)

def _set_HSTR_EL2_Type_T5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T5 r v)

def _set_HSTR_Type_T5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T5 r v)

def _set_HSTR_EL2_Type_T6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T6 r v)

def _set_HSTR_Type_T6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T6 r v)

def _set_HSTR_EL2_Type_T7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T7 r v)

def _set_HSTR_Type_T7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T7 r v)

def _set_HSTR_EL2_Type_T8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T8 r v)

def _set_HSTR_Type_T8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T8 r v)

def _set_HSTR_EL2_Type_T9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_EL2_Type_T9 r v)

def _set_HSTR_Type_T9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HSTR_Type_T9 r v)

def EffectiveMDSELR_EL1_BANK (_ : Unit) : SailM (BitVec 2) := do
  let num_bp ← do (NumBreakpointsImplemented ())
  let num_wp ← do (NumWatchpointsImplemented ())
  if (((num_bp ≤b 16) && (num_wp ≤b 16)) : Bool)
  then (pure 0b00#2)
  else
    (do
      if ((←((pure (HaveEL EL3)) <&&> (do
           (pure ((_get_MDCR_EL3_Type_EBWE (← readReg MDCR_EL3)) == 0#1))) <||> (do
           (pure ((← readReg PSTATE).EL != EL3)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure ((_get_MDCR_EL2_Type_EBWE (← readReg MDCR_EL2)) == 0#1)))) <||> (do
           (pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (pure ((_get_MDSCR_EL1_Type_EMBWE (← readReg MDSCR_EL1)) == 0#1)))))) : Bool)
      then (pure 0b00#2)
      else
        (do
          let bank ← (( do (pure (_get_MDSELR_EL1_Type_BANK (← readReg MDSELR_EL1))) ) : SailM (BitVec 2) )
          if (((((bank == 0b11#2) && (num_bp ≤b 48)) && (num_wp ≤b 48)) || (((bank == 0b10#2) && (num_bp ≤b 32)) && (num_wp ≤b 32))) : Bool)
          then
            (do
              let (_, __tup_1) ← do (ConstrainUnpredictableBits Unpredictable_RESMDSELR 2)
              (pure __tup_1))
          else (pure bank)))

def AArch64_ClearEventCounters (_ : Unit) : SailM Unit := do
  let counters ← do (AArch64_GetNumEventCountersAccessible ())
  if ((counters != 0) : Bool)
  then
    (do
      let loop_idx_lower := 0
      let loop_idx_upper := (counters -i 1)
      let mut loop_vars := ()
      for idx in [loop_idx_lower:loop_idx_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          sail_assert ((0 ≤b idx) && (idx <b 32)) "src/v8_base.sail:34397.64-34397.65"
          writeReg PMEVCNTR_EL0 (vectorUpdate (← readReg PMEVCNTR_EL0) idx (Zeros (n := 64)))
      (pure loop_vars))
  else (pure ())

def AArch64_PMUSwIncrement (sw_incr : (BitVec 32)) : SailM Unit := do
  if ((←((pure ((_get_PMCR_EL0_Type_E (← readReg PMCR_EL0)) == 0#1)) <&&> (do
       (pure ((_get_MDCR_EL2_Type_HPME (← readReg MDCR_EL2)) == 0#1))))) : Bool)
  then (pure ())
  else
    (do
      let counters ← do (AArch64_GetNumEventCountersAccessible ())
      if ((counters != 0) : Bool)
      then
        (do
          let loop_idx_lower := 0
          let loop_idx_upper := (counters -i 1)
          let mut loop_vars := ()
          for idx in [loop_idx_lower:loop_idx_upper:1]i do
            let () := loop_vars
            loop_vars ← do
              sail_assert ((0 ≤b idx) && (idx <b 32)) "src/v8_base.sail:34413.64-34413.65"
              if (((BitVec.join1 [(BitVec.access sw_incr idx)]) == 1#1) : Bool)
              then (PMUEvent__2 PMU_EVENT_SW_INCR 1 idx)
              else (pure ())
          (pure loop_vars))
      else (pure ()))

def _set_PMCCNTR_EL0_Type_CCNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCNTR_EL0_Type_CCNT r v)

def _set_PMCCNTR_Type_CCNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCNTR_Type_CCNT r v)

def _set_PMCCNTSVR_EL1_Type_CCNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCCNTSVR_EL1_Type_CCNT r v)

def SPESampleAddAddressPCVirtual (_ : Unit) : SailM Unit := do
  let this_address ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  writeReg SPESampleAddress (vectorUpdate (← readReg SPESampleAddress) SPEAddrPosPCVirtual (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg SPESampleAddress) SPEAddrPosPCVirtual) 55 0 (Sail.BitVec.extractLsb this_address 55 0)))
  let ns ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let nse ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (ns, nse) ← (( do
    match (← (CurrentSecurityState ())) with
    | .SS_Secure =>
      (let ns : (BitVec 1) := 0#1
      let nse : (BitVec 1) := 0#1
      (pure (ns, nse)))
    | .SS_NonSecure =>
      (let ns : (BitVec 1) := 1#1
      let nse : (BitVec 1) := 0#1
      (pure (ns, nse)))
    | .SS_Realm =>
      (let ns : (BitVec 1) := 1#1
      let nse : (BitVec 1) := 1#1
      (pure (ns, nse)))
    | _ =>
      (do
        (Unreachable ())
        (pure (ns, nse))) ) : SailM ((BitVec 1) × (BitVec 1)) )
  let el ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  writeReg SPESampleAddress (vectorUpdate (← readReg SPESampleAddress) SPEAddrPosPCVirtual (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg SPESampleAddress) SPEAddrPosPCVirtual) 63 56 (((ns +++ el) +++ nse) +++ (Zeros (n := 4)))))
  writeReg SPESampleAddressValid (vectorUpdate (← readReg SPESampleAddressValid) SPEAddrPosPCVirtual true)

def CollectContextIDR1 (_ : Unit) : SailM Bool := do
  if ((! (← (StatisticalProfilingEnabled ()))) : Bool)
  then (pure false)
  else
    (do
      if (((← readReg PSTATE).EL == EL2) : Bool)
      then (pure false)
      else
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
          then (pure false)
          else (pure ((_get_PMSCR_EL1_Type_CX (← readReg PMSCR_EL1)) == 1#1))))

def CollectContextIDR2 (_ : Unit) : SailM Bool := do
  if ((! (← (StatisticalProfilingEnabled ()))) : Bool)
  then (pure false)
  else
    (do
      if ((! (← (EL2Enabled ()))) : Bool)
      then (pure false)
      else (pure ((_get_PMSCR_EL2_Type_CX (← readReg PMSCR_EL2)) == 1#1)))

def CollectTimeStamp (_ : Unit) : SailM TimeStamp := SailME.run do
  let owning_el ← (( do (undefined_bitvector 2) ) : SailME TimeStamp (BitVec 2) )
  if ((! (← (StatisticalProfilingEnabled ()))) : Bool)
  then (pure TimeStamp_None)
  else
    (do
      let owning_el ← (( do
        let (_, __tup_1) ← do (ProfilingBufferOwner ())
        (pure __tup_1) ) : SailME TimeStamp (BitVec 2) )
      if ((owning_el == EL2) : Bool)
      then
        (do
          if (((_get_PMSCR_EL2_Type_TS (← readReg PMSCR_EL2)) == 0#1) : Bool)
          then SailME.throw (TimeStamp_None : TimeStamp)
          else (pure ()))
      else
        (do
          if (((_get_PMSCR_EL1_Type_TS (← readReg PMSCR_EL1)) == 0#1) : Bool)
          then SailME.throw (TimeStamp_None : TimeStamp)
          else (pure ()))
      let PCT_el1 ← (( do (undefined_bitvector 2) ) : SailME TimeStamp (BitVec 2) )
      let PCT_el1 ← (( do
        if ((! (← (HaveECVExt ()))) : Bool)
        then (do (pure (0#1 +++ (BitVec.join1 [(BitVec.access (_get_PMSCR_EL1_Type_PCT (← readReg PMSCR_EL1)) 0)]))))
        else
          (do
            let PCT_el1 ← (pure (_get_PMSCR_EL1_Type_PCT (← readReg PMSCR_EL1)))
            if ((PCT_el1 == 0b10#2) : Bool)
            then
              (do
                let (_, __tup_1) ← do (ConstrainUnpredictableBits Unpredictable_PMSCR_PCT 2)
                (pure __tup_1))
            else (pure PCT_el1)) ) : SailME TimeStamp (BitVec 2) )
      if ((← (EL2Enabled ())) : Bool)
      then
        (do
          let PCT_el2 ← (( do (undefined_bitvector 2) ) : SailME TimeStamp (BitVec 2) )
          let PCT_el2 ← (( do
            if ((! (← (HaveECVExt ()))) : Bool)
            then (do (pure (0#1 +++ (BitVec.join1 [(BitVec.access (_get_PMSCR_EL2_Type_PCT (← readReg PMSCR_EL2)) 0)]))))
            else
              (do
                let PCT_el2 ← (pure (_get_PMSCR_EL2_Type_PCT (← readReg PMSCR_EL2)))
                if ((PCT_el2 == 0b10#2) : Bool)
                then
                  (do
                    let (_, __tup_1) ← do (ConstrainUnpredictableBits Unpredictable_PMSCR_PCT 2)
                    (pure __tup_1))
                else (pure PCT_el2)) ) : SailME TimeStamp (BitVec 2) )
          match (PCT_el2 : BitVec 2) with
          | 0b00 =>
            SailME.throw (← (do
                if ((← (IsInHost ())) : Bool)
                then (pure TimeStamp_Physical)
                else (pure TimeStamp_Virtual)))
          | 0b01 =>
            (do
              if ((owning_el == EL2) : Bool)
              then SailME.throw (TimeStamp_Physical : TimeStamp)
              else (pure ()))
          | 0b11 =>
            SailME.throw (← (do
                sail_assert (← (HaveECVExt ())) "src/v8_base.sail:34626.33-34626.34"
                if (((owning_el == EL1) && (PCT_el1 == 0b00#2)) : Bool)
                then
                  (do
                    if ((← (IsInHost ())) : Bool)
                    then (pure TimeStamp_Physical)
                    else (pure TimeStamp_Virtual))
                else (pure TimeStamp_OffsetPhysical)))
          | _ => (Unreachable ()))
      else (pure ())
      match (PCT_el1 : BitVec 2) with
      | 0b00 =>
        (do
          if ((← (IsInHost ())) : Bool)
          then (pure TimeStamp_Physical)
          else (pure TimeStamp_Virtual))
      | 0b01 => (pure TimeStamp_Physical)
      | 0b11 =>
        (do
          sail_assert (← (HaveECVExt ())) "src/v8_base.sail:34647.29-34647.30"
          (pure TimeStamp_OffsetPhysical))
      | _ =>
        (do
          (Unreachable ())
          (undefined_TimeStamp ())))

def _set_PMSICR_EL1_Type_COUNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSICR_EL1_Type_COUNT r v)

def _set_PMSICR_EL1_Type_ECOUNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSICR_EL1_Type_ECOUNT r v)

def _set_PMSIRR_EL1_Type_INTERVAL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIRR_EL1_Type_INTERVAL r v)

def _set_PMSIRR_EL1_Type_RND (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSIRR_EL1_Type_RND r v)

def SPEBufferFilled (_ : Unit) : SailM Unit := do
  if ((IsZero (_get_PMBSR_EL1_Type_S (← readReg PMBSR_EL1))) : Bool)
  then
    (do
      writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange (← readReg PMBSR_EL1) 17 17 1#1)
      writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange (← readReg PMBSR_EL1) 31 26 0b000000#6)
      writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange (← readReg PMBSR_EL1) 15 0 (Sail.BitVec.zeroExtend 0b000001#6 16)))
  else (pure ())
  (PMUEvent PMU_EVENT_SAMPLE_WRAP)

def SPEBufferIsFull (_ : Unit) : SailM Bool := do
  let write_pointer_limit ← do (pure (BitVec.toNat ((_get_PMBLIMITR_EL1_Type_LIMIT (← readReg PMBLIMITR_EL1)) +++ (Zeros (n := 12)))))
  let current_write_pointer ← do (pure (BitVec.toNat (← readReg PMBPTR_EL1)))
  let record_max_size ← do (pure (Int.shiftl 1 (BitVec.toNat (_get_PMSIDR_EL1_Type_MaxSize (← readReg PMSIDR_EL1)))))
  (pure (current_write_pointer >b (write_pointer_limit -i record_max_size)))

def _set_PMSDSFR_EL1_Type_S0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S0 r v)

def _set_ERXGSR_EL1_Type_S0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S0 r v)

def _set_PMSDSFR_EL1_Type_S1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S1 r v)

def _set_ERXGSR_EL1_Type_S1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S1 r v)

def _set_PMSDSFR_EL1_Type_S10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S10 r v)

def _set_ERXGSR_EL1_Type_S10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S10 r v)

def _set_PMSDSFR_EL1_Type_S11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S11 r v)

def _set_ERXGSR_EL1_Type_S11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S11 r v)

def _set_PMSDSFR_EL1_Type_S12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S12 r v)

def _set_ERXGSR_EL1_Type_S12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S12 r v)

def _set_PMSDSFR_EL1_Type_S13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S13 r v)

def _set_ERXGSR_EL1_Type_S13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S13 r v)

def _set_PMSDSFR_EL1_Type_S14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S14 r v)

def _set_ERXGSR_EL1_Type_S14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S14 r v)

def _set_PMSDSFR_EL1_Type_S15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S15 r v)

def _set_ERXGSR_EL1_Type_S15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S15 r v)

def _set_PMSDSFR_EL1_Type_S16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S16 r v)

def _set_ERXGSR_EL1_Type_S16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S16 r v)

def _set_PMSDSFR_EL1_Type_S17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S17 r v)

def _set_ERXGSR_EL1_Type_S17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S17 r v)

def _set_PMSDSFR_EL1_Type_S18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S18 r v)

def _set_ERXGSR_EL1_Type_S18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S18 r v)

def _set_PMSDSFR_EL1_Type_S19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S19 r v)

def _set_ERXGSR_EL1_Type_S19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S19 r v)

def _set_PMSDSFR_EL1_Type_S2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S2 r v)

def _set_ERXGSR_EL1_Type_S2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S2 r v)

def _set_PMSDSFR_EL1_Type_S20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S20 r v)

def _set_ERXGSR_EL1_Type_S20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S20 r v)

def _set_PMSDSFR_EL1_Type_S21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S21 r v)

def _set_ERXGSR_EL1_Type_S21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S21 r v)

def _set_PMSDSFR_EL1_Type_S22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S22 r v)

def _set_ERXGSR_EL1_Type_S22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S22 r v)

def _set_PMSDSFR_EL1_Type_S23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S23 r v)

def _set_ERXGSR_EL1_Type_S23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S23 r v)

def _set_PMSDSFR_EL1_Type_S24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S24 r v)

def _set_ERXGSR_EL1_Type_S24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S24 r v)

def _set_PMSDSFR_EL1_Type_S25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S25 r v)

def _set_ERXGSR_EL1_Type_S25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S25 r v)

def _set_PMSDSFR_EL1_Type_S26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S26 r v)

def _set_ERXGSR_EL1_Type_S26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S26 r v)

def _set_PMSDSFR_EL1_Type_S27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S27 r v)

def _set_ERXGSR_EL1_Type_S27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S27 r v)

def _set_PMSDSFR_EL1_Type_S28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S28 r v)

def _set_ERXGSR_EL1_Type_S28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S28 r v)

def _set_PMSDSFR_EL1_Type_S29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S29 r v)

def _set_ERXGSR_EL1_Type_S29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S29 r v)

def _set_PMSDSFR_EL1_Type_S3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S3 r v)

def _set_ERXGSR_EL1_Type_S3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S3 r v)

def _set_PMSDSFR_EL1_Type_S30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S30 r v)

def _set_ERXGSR_EL1_Type_S30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S30 r v)

def _set_PMSDSFR_EL1_Type_S31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S31 r v)

def _set_ERXGSR_EL1_Type_S31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S31 r v)

def _set_PMSDSFR_EL1_Type_S32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S32 r v)

def _set_ERXGSR_EL1_Type_S32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S32 r v)

def _set_PMSDSFR_EL1_Type_S33 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S33 r v)

def _set_ERXGSR_EL1_Type_S33 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S33 r v)

def _set_PMSDSFR_EL1_Type_S34 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S34 r v)

def _set_ERXGSR_EL1_Type_S34 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S34 r v)

def _set_PMSDSFR_EL1_Type_S35 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S35 r v)

def _set_ERXGSR_EL1_Type_S35 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S35 r v)

def _set_PMSDSFR_EL1_Type_S36 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S36 r v)

def _set_ERXGSR_EL1_Type_S36 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S36 r v)

def _set_PMSDSFR_EL1_Type_S37 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S37 r v)

def _set_ERXGSR_EL1_Type_S37 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S37 r v)

def _set_PMSDSFR_EL1_Type_S38 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S38 r v)

def _set_ERXGSR_EL1_Type_S38 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S38 r v)

def _set_PMSDSFR_EL1_Type_S39 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S39 r v)

def _set_ERXGSR_EL1_Type_S39 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S39 r v)

def _set_PMSDSFR_EL1_Type_S4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S4 r v)

def _set_ERXGSR_EL1_Type_S4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S4 r v)

def _set_PMSDSFR_EL1_Type_S40 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S40 r v)

def _set_ERXGSR_EL1_Type_S40 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S40 r v)

def _set_PMSDSFR_EL1_Type_S41 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S41 r v)

def _set_ERXGSR_EL1_Type_S41 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S41 r v)

def _set_PMSDSFR_EL1_Type_S42 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S42 r v)

def _set_ERXGSR_EL1_Type_S42 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S42 r v)

def _set_PMSDSFR_EL1_Type_S43 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S43 r v)

def _set_ERXGSR_EL1_Type_S43 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S43 r v)

def _set_PMSDSFR_EL1_Type_S44 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S44 r v)

def _set_ERXGSR_EL1_Type_S44 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S44 r v)

def _set_PMSDSFR_EL1_Type_S45 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S45 r v)

def _set_ERXGSR_EL1_Type_S45 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S45 r v)

def _set_PMSDSFR_EL1_Type_S46 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S46 r v)

def _set_ERXGSR_EL1_Type_S46 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S46 r v)

def _set_PMSDSFR_EL1_Type_S47 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S47 r v)

def _set_ERXGSR_EL1_Type_S47 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S47 r v)

def _set_PMSDSFR_EL1_Type_S48 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S48 r v)

def _set_ERXGSR_EL1_Type_S48 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S48 r v)

def _set_PMSDSFR_EL1_Type_S49 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S49 r v)

def _set_ERXGSR_EL1_Type_S49 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S49 r v)

def _set_PMSDSFR_EL1_Type_S5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S5 r v)

def _set_ERXGSR_EL1_Type_S5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S5 r v)

def _set_PMSDSFR_EL1_Type_S50 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S50 r v)

def _set_ERXGSR_EL1_Type_S50 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S50 r v)

def _set_PMSDSFR_EL1_Type_S51 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S51 r v)

def _set_ERXGSR_EL1_Type_S51 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S51 r v)

def _set_PMSDSFR_EL1_Type_S52 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S52 r v)

def _set_ERXGSR_EL1_Type_S52 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S52 r v)

def _set_PMSDSFR_EL1_Type_S53 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S53 r v)

def _set_ERXGSR_EL1_Type_S53 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S53 r v)

def _set_PMSDSFR_EL1_Type_S54 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S54 r v)

def _set_ERXGSR_EL1_Type_S54 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S54 r v)

def _set_PMSDSFR_EL1_Type_S55 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S55 r v)

def _set_ERXGSR_EL1_Type_S55 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S55 r v)

def _set_PMSDSFR_EL1_Type_S56 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S56 r v)

def _set_ERXGSR_EL1_Type_S56 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S56 r v)

def _set_PMSDSFR_EL1_Type_S57 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S57 r v)

def _set_ERXGSR_EL1_Type_S57 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S57 r v)

def _set_PMSDSFR_EL1_Type_S58 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S58 r v)

def _set_ERXGSR_EL1_Type_S58 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S58 r v)

def _set_PMSDSFR_EL1_Type_S59 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S59 r v)

def _set_ERXGSR_EL1_Type_S59 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S59 r v)

def _set_PMSDSFR_EL1_Type_S6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S6 r v)

def _set_ERXGSR_EL1_Type_S6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S6 r v)

def _set_PMSDSFR_EL1_Type_S60 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S60 r v)

def _set_ERXGSR_EL1_Type_S60 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S60 r v)

def _set_PMSDSFR_EL1_Type_S61 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S61 r v)

def _set_ERXGSR_EL1_Type_S61 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S61 r v)

def _set_PMSDSFR_EL1_Type_S62 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S62 r v)

def _set_ERXGSR_EL1_Type_S62 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S62 r v)

def _set_PMSDSFR_EL1_Type_S63 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S63 r v)

def _set_ERXGSR_EL1_Type_S63 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S63 r v)

def _set_PMSDSFR_EL1_Type_S7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S7 r v)

def _set_ERXGSR_EL1_Type_S7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S7 r v)

def _set_PMSDSFR_EL1_Type_S8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S8 r v)

def _set_ERXGSR_EL1_Type_S8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S8 r v)

def _set_PMSDSFR_EL1_Type_S9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSDSFR_EL1_Type_S9 r v)

def _set_ERXGSR_EL1_Type_S9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERXGSR_EL1_Type_S9 r v)

def _set_PMSEVFR_EL1_Type_E1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E1 r v)

def _set_PMSNEVFR_EL1_Type_E1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E1 r v)

def _set_PMSEVFR_EL1_Type_E10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E10 r v)

def _set_PMSNEVFR_EL1_Type_E10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E10 r v)

def _set_PMSEVFR_EL1_Type_E11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E11 r v)

def _set_PMSNEVFR_EL1_Type_E11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E11 r v)

def _set_PMSEVFR_EL1_Type_E12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E12 r v)

def _set_PMSNEVFR_EL1_Type_E12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E12 r v)

def _set_PMSEVFR_EL1_Type_E13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E13 r v)

def _set_PMSNEVFR_EL1_Type_E13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E13 r v)

def _set_PMSEVFR_EL1_Type_E14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E14 r v)

def _set_PMSNEVFR_EL1_Type_E14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E14 r v)

def _set_PMSEVFR_EL1_Type_E15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E15 r v)

def _set_PMSNEVFR_EL1_Type_E15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E15 r v)

def _set_PMSEVFR_EL1_Type_E16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E16 r v)

def _set_PMSNEVFR_EL1_Type_E16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E16 r v)

def _set_PMSEVFR_EL1_Type_E17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E17 r v)

def _set_PMSNEVFR_EL1_Type_E17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E17 r v)

def _set_PMSEVFR_EL1_Type_E18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E18 r v)

def _set_PMSNEVFR_EL1_Type_E18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E18 r v)

def _set_PMSEVFR_EL1_Type_E19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E19 r v)

def _set_PMSNEVFR_EL1_Type_E19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E19 r v)

def _set_PMSEVFR_EL1_Type_E2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E2 r v)

def _set_EDVIDSR_Type_E2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDVIDSR_Type_E2 r v)

def _set_PMSNEVFR_EL1_Type_E2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E2 r v)

def _set_PMSEVFR_EL1_Type_E20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E20 r v)

def _set_PMSNEVFR_EL1_Type_E20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E20 r v)

def _set_PMSEVFR_EL1_Type_E21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E21 r v)

def _set_PMSNEVFR_EL1_Type_E21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E21 r v)

def _set_PMSEVFR_EL1_Type_E22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E22 r v)

def _set_PMSNEVFR_EL1_Type_E22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E22 r v)

def _set_PMSEVFR_EL1_Type_E23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E23 r v)

def _set_PMSNEVFR_EL1_Type_E23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E23 r v)

def _set_PMSEVFR_EL1_Type_E24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E24 r v)

def _set_PMSNEVFR_EL1_Type_E24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E24 r v)

def _set_PMSEVFR_EL1_Type_E25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E25 r v)

def _set_PMSNEVFR_EL1_Type_E25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E25 r v)

def _set_PMSEVFR_EL1_Type_E26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E26 r v)

def _set_PMSNEVFR_EL1_Type_E26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E26 r v)

def _set_PMSEVFR_EL1_Type_E27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E27 r v)

def _set_PMSNEVFR_EL1_Type_E27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E27 r v)

def _set_PMSEVFR_EL1_Type_E28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E28 r v)

def _set_PMSNEVFR_EL1_Type_E28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E28 r v)

def _set_PMSEVFR_EL1_Type_E29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E29 r v)

def _set_PMSNEVFR_EL1_Type_E29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E29 r v)

def _set_PMSEVFR_EL1_Type_E3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E3 r v)

def _set_EDVIDSR_Type_E3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDVIDSR_Type_E3 r v)

def _set_PMSNEVFR_EL1_Type_E3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E3 r v)

def _set_PMSEVFR_EL1_Type_E30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E30 r v)

def _set_PMSNEVFR_EL1_Type_E30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E30 r v)

def _set_PMSEVFR_EL1_Type_E31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E31 r v)

def _set_PMSNEVFR_EL1_Type_E31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E31 r v)

def _set_PMSEVFR_EL1_Type_E4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E4 r v)

def _set_PMSNEVFR_EL1_Type_E4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E4 r v)

def _set_PMSEVFR_EL1_Type_E48 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E48 r v)

def _set_PMSNEVFR_EL1_Type_E48 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E48 r v)

def _set_PMSEVFR_EL1_Type_E49 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E49 r v)

def _set_PMSNEVFR_EL1_Type_E49 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E49 r v)

def _set_PMSEVFR_EL1_Type_E5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E5 r v)

def _set_PMSNEVFR_EL1_Type_E5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E5 r v)

def _set_PMSEVFR_EL1_Type_E50 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E50 r v)

def _set_PMSNEVFR_EL1_Type_E50 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E50 r v)

def _set_PMSEVFR_EL1_Type_E51 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E51 r v)

def _set_PMSNEVFR_EL1_Type_E51 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E51 r v)

def _set_PMSEVFR_EL1_Type_E52 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E52 r v)

def _set_PMSNEVFR_EL1_Type_E52 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E52 r v)

def _set_PMSEVFR_EL1_Type_E53 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E53 r v)

def _set_PMSNEVFR_EL1_Type_E53 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E53 r v)

def _set_PMSEVFR_EL1_Type_E54 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E54 r v)

def _set_PMSNEVFR_EL1_Type_E54 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E54 r v)

def _set_PMSEVFR_EL1_Type_E55 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E55 r v)

def _set_PMSNEVFR_EL1_Type_E55 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E55 r v)

def _set_PMSEVFR_EL1_Type_E56 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E56 r v)

def _set_PMSNEVFR_EL1_Type_E56 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E56 r v)

def _set_PMSEVFR_EL1_Type_E57 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E57 r v)

def _set_PMSNEVFR_EL1_Type_E57 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E57 r v)

def _set_PMSEVFR_EL1_Type_E58 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E58 r v)

def _set_PMSNEVFR_EL1_Type_E58 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E58 r v)

def _set_PMSEVFR_EL1_Type_E59 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E59 r v)

def _set_PMSNEVFR_EL1_Type_E59 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E59 r v)

def _set_PMSEVFR_EL1_Type_E6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E6 r v)

def _set_PMSNEVFR_EL1_Type_E6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E6 r v)

def _set_PMSEVFR_EL1_Type_E60 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E60 r v)

def _set_PMSNEVFR_EL1_Type_E60 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E60 r v)

def _set_PMSEVFR_EL1_Type_E61 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E61 r v)

def _set_PMSNEVFR_EL1_Type_E61 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E61 r v)

def _set_PMSEVFR_EL1_Type_E62 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E62 r v)

def _set_PMSNEVFR_EL1_Type_E62 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E62 r v)

def _set_PMSEVFR_EL1_Type_E63 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E63 r v)

def _set_PMSNEVFR_EL1_Type_E63 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E63 r v)

def _set_PMSEVFR_EL1_Type_E7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E7 r v)

def _set_PMSNEVFR_EL1_Type_E7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E7 r v)

def _set_PMSEVFR_EL1_Type_E8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E8 r v)

def _set_PMSNEVFR_EL1_Type_E8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E8 r v)

def _set_PMSEVFR_EL1_Type_E9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSEVFR_EL1_Type_E9 r v)

def _set_PMSNEVFR_EL1_Type_E9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSNEVFR_EL1_Type_E9 r v)

def _set_PMSFCR_EL1_Type_B (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_B r v)

def _set_PMSFCR_EL1_Type_LD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_LD r v)

def _set_LORID_EL1_Type_LD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORID_EL1_Type_LD r v)

def _set_PMSLATFR_EL1_Type_MINLAT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSLATFR_EL1_Type_MINLAT r v)

/-- Type quantifiers: total_latency : Int -/
def SPECollectRecord (events : (BitVec 64)) (total_latency : Int) (optype : OpType) : SailM Bool := do
  sail_assert (← (StatisticalProfilingEnabled ())) "src/v8_base.sail:34983.40-34983.41"
  let mask : (BitVec 64) := (Sail.BitVec.zeroExtend 0xAA#8 64)
  let m ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do
    if ((← (HaveSVE ())) : Bool)
    then (pure (Sail.BitVec.updateSubrange mask 18 17 0b11#2))
    else (pure mask) ) : SailM (BitVec 64) )
  let mask ← (( do
    if ((← (HaveTME ())) : Bool)
    then (pure (BitVec.update mask 16 (Bit 1#1)))
    else (pure mask) ) : SailM (BitVec 64) )
  let mask ← (( do
    if ((← (HaveStatisticalProfilingv1p1 ())) : Bool)
    then (pure (BitVec.update mask 11 (Bit 1#1)))
    else (pure mask) ) : SailM (BitVec 64) )
  let mask ← (( do
    if ((← (HaveStatisticalProfilingv1p2 ())) : Bool)
    then (pure (BitVec.update mask 6 (Bit 1#1)))
    else (pure mask) ) : SailM (BitVec 64) )
  let mask ← (( do
    if ((← (HaveStatisticalProfilingv1p4 ())) : Bool)
    then
      (let mask : (BitVec 64) := (Sail.BitVec.updateSubrange mask 10 8 (Sail.BitVec.extractLsb 0b11111#5 4 2))
      let mask : (BitVec 64) := (Sail.BitVec.updateSubrange mask 4 4 (Sail.BitVec.extractLsb 0b11111#5 1 1))
      (pure (Sail.BitVec.updateSubrange mask 2 2 (Sail.BitVec.extractLsb 0b11111#5 0 0))))
    else
      (do
        let impdef_mask ← (( do (__IMPDEF_bits 5 "SPE mask 10:8,4,2") ) : SailM (BitVec 5) )
        let mask : (BitVec 64) := (Sail.BitVec.updateSubrange mask 10 8 (Sail.BitVec.extractLsb impdef_mask 4 2))
        let mask : (BitVec 64) := (Sail.BitVec.updateSubrange mask 4 4 (Sail.BitVec.extractLsb impdef_mask 1 1))
        (pure (Sail.BitVec.updateSubrange mask 2 2 (Sail.BitVec.extractLsb impdef_mask 0 0)))) ) : SailM (BitVec 64) )
  let mask ← (pure (Sail.BitVec.updateSubrange mask 63 48 (← (__IMPDEF_bits 16 "SPE mask 63:48"))))
  let mask ← (pure (Sail.BitVec.updateSubrange mask 31 24 (← (__IMPDEF_bits 8 "SPE mask 31:24"))))
  let mask ← (pure (Sail.BitVec.updateSubrange mask 15 12 (← (__IMPDEF_bits 4 "SPE mask 15:12"))))
  let e : (BitVec 64) := (events &&& mask)
  let is_rejected_nevent : Bool := false
  let is_nevt ← (( do (undefined_bool ()) ) : SailM Bool )
  let (is_nevt, is_rejected_nevent, m) ← (( do
    if ((← (HaveStatisticalProfilingv1p2 ())) : Bool)
    then
      (do
        let m ← (pure ((← readReg PMSNEVFR_EL1) &&& mask))
        let is_nevt : Bool := (IsZero (e &&& m))
        let is_rejected_nevent ← (( do
          if (((_get_PMSFCR_EL1_Type_FnE (← readReg PMSFCR_EL1)) == 1#1) : Bool)
          then
            (do
              if ((! (IsZero m)) : Bool)
              then (pure (! is_nevt))
              else (do (ConstrainUnpredictableBool Unpredictable_BADPMSFCR)))
          else (pure is_rejected_nevent) ) : SailM Bool )
        (pure (is_nevt, is_rejected_nevent, m)))
    else
      (let is_nevt : Bool := true
      (pure (is_nevt, is_rejected_nevent, m))) ) : SailM (Bool × Bool × (BitVec 64)) )
  let is_rejected_event : Bool := false
  let m ← (( do (pure ((← readReg PMSEVFR_EL1) &&& mask)) ) : SailM (BitVec 64) )
  let is_evt : Bool := (IsZero ((Complement.complement e) &&& m))
  let is_rejected_event ← (( do
    if (((_get_PMSFCR_EL1_Type_FE (← readReg PMSFCR_EL1)) == 1#1) : Bool)
    then
      (do
        if ((! (IsZero m)) : Bool)
        then (pure (! is_evt))
        else (do (ConstrainUnpredictableBool Unpredictable_BADPMSFCR)))
    else (pure is_rejected_event) ) : SailM Bool )
  let (is_rejected_event, is_rejected_nevent) ← (( do
    if ((←((HaveStatisticalProfilingv1p2 ()) <&&> (do
         (pure (((_get_PMSFCR_EL1_Type_FnE (← readReg PMSFCR_EL1)) +++ (_get_PMSFCR_EL1_Type_FE (← readReg PMSFCR_EL1))) == 0b11#2))) <&&> (do
         (pure (! (IsZero (((← readReg PMSEVFR_EL1) &&& (← readReg PMSNEVFR_EL1)) &&& mask))))))) : Bool)
    then
      (do
        let is_rejected_nevent ← (ConstrainUnpredictableBool Unpredictable_BADPMSFCR)
        let is_rejected_event ← (ConstrainUnpredictableBool Unpredictable_BADPMSFCR)
        (pure (is_rejected_event, is_rejected_nevent)))
    else (pure (is_rejected_event, is_rejected_nevent)) ) : SailM (Bool × Bool) )
  if ((is_evt && is_nevt) : Bool)
  then (PMUEvent PMU_EVENT_SAMPLE_FEED_EVENT)
  else (pure ())
  let is_op_br : Bool := false
  let is_op_ld : Bool := false
  let is_op_st : Bool := false
  let is_op_br : Bool := (BEq.beq optype OpType_Branch)
  let is_op_ld : Bool := ((BEq.beq optype OpType_Load) || (BEq.beq optype OpType_LoadAtomic))
  let is_op_st : Bool := ((BEq.beq optype OpType_Store) || (BEq.beq optype OpType_LoadAtomic))
  if (is_op_br : Bool)
  then (PMUEvent PMU_EVENT_SAMPLE_FEED_BR)
  else (pure ())
  if (is_op_ld : Bool)
  then (PMUEvent PMU_EVENT_SAMPLE_FEED_LD)
  else (pure ())
  if (is_op_st : Bool)
  then (PMUEvent PMU_EVENT_SAMPLE_FEED_ST)
  else (pure ())
  let is_op ← (( do (pure is_op_br) <&&> (do (pure ((_get_PMSFCR_EL1_Type_B (← readReg PMSFCR_EL1)) == 1#1))) <||> (do (pure is_op_ld) <&&> (do (pure ((_get_PMSFCR_EL1_Type_LD (← readReg PMSFCR_EL1)) == 1#1)))) <||> (do (pure is_op_st) <&&> (do (pure ((_get_PMSFCR_EL1_Type_ST (← readReg PMSFCR_EL1)) == 1#1)))) ) : SailM Bool )
  if (is_op : Bool)
  then (PMUEvent PMU_EVENT_SAMPLE_FEED_OP)
  else (pure ())
  let is_rejected_type : Bool := false
  let is_rejected_type ← (( do
    if (((_get_PMSFCR_EL1_Type_FT (← readReg PMSFCR_EL1)) == 1#1) : Bool)
    then
      (do
        if ((! (IsZero ((_get_PMSFCR_EL1_Type_B (← readReg PMSFCR_EL1)) +++ ((_get_PMSFCR_EL1_Type_LD (← readReg PMSFCR_EL1)) +++ (_get_PMSFCR_EL1_Type_ST (← readReg PMSFCR_EL1)))))) : Bool)
        then (pure (! is_op))
        else (do (ConstrainUnpredictableBool Unpredictable_BADPMSFCR)))
    else (pure is_rejected_type) ) : SailM Bool )
  let is_rejected_latency : Bool := false
  let is_lat ← (( do (pure (total_latency <b (BitVec.toNat (_get_PMSLATFR_EL1_Type_MINLAT (← readReg PMSLATFR_EL1))))) ) : SailM Bool )
  if (is_lat : Bool)
  then (PMUEvent PMU_EVENT_SAMPLE_FEED_LAT)
  else (pure ())
  let is_rejected_latency ← (( do
    if (((_get_PMSFCR_EL1_Type_FL (← readReg PMSFCR_EL1)) == 1#1) : Bool)
    then
      (do
        if ((! (IsZero (_get_PMSLATFR_EL1_Type_MINLAT (← readReg PMSLATFR_EL1)))) : Bool)
        then (pure (! is_lat))
        else (do (ConstrainUnpredictableBool Unpredictable_BADPMSFCR)))
    else (pure is_rejected_latency) ) : SailM Bool )
  let is_rejected_data_source ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((←((pure ((←((HaveStatisticalProfilingFDS ()) <&&> (do (pure ((_get_PMSFCR_EL1_Type_FDS (← readReg PMSFCR_EL1)) == 1#1))))) && is_op_ld)) <&&> (do
       readReg SPESampleDataSourceValid))) : Bool)
  then
    (do
      let data_source ← (( do readReg SPESampleDataSource ) : SailM (BitVec 16) )
      let index := (BitVec.toNat (Sail.BitVec.extractLsb data_source 5 0))
      let is_rejected_data_source ← (pure ((BitVec.join1 [(BitVec.access (← readReg PMSDSFR_EL1) index)]) == 0#1))
      (pure ()))
  else
    (let is_rejected_data_source : Bool := false
    (pure ()))
  let return_value : Bool := (! (((is_rejected_nevent || is_rejected_event) || is_rejected_type) || is_rejected_latency))
  if (return_value : Bool)
  then (PMUEvent PMU_EVENT_SAMPLE_FILTRATE)
  else (pure ())
  (pure return_value)

def _set_PMBIDR_EL1_Type_Align (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMBIDR_EL1_Type_Align r v)

def SPEAddByteToRecord (b : (BitVec 8)) : SailM Unit := do
  let size ← do readReg SPERecordSize
  sail_assert ((0 ≤b size) && (size <b SPEMaxRecordSize)) "src/v8_base.sail:35106.46-35106.47"
  writeReg SPERecordData (vectorUpdate (← readReg SPERecordData) size b)
  writeReg SPERecordSize (size +i 1)

def SPEEmptyRecord (_ : Unit) : SailM Unit := do
  writeReg SPERecordSize 0
  let loop_i_lower := 0
  let loop_i_upper := (SPEMaxRecordSize -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do writeReg SPERecordData (vectorUpdate (← readReg SPERecordData) i (Zeros (n := 8)))
  (pure loop_vars)

/-- Type quantifiers: k_aligned : Bool -/
def DebugMemWrite (vaddress : (BitVec 64)) (accdesc : AccessDescriptor) (aligned : Bool) (data : (BitVec 8)) : SailM (PhysMemRetStatus × AddressDescriptor) := do
  let memstatus ← (( do (__UNKNOWN_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
  let size := 1
  let addrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) : SailM AddressDescriptor )
  if ((IsFault addrdesc) : Bool)
  then (pure (memstatus, addrdesc))
  else
    (do
      let memstatus ← (( do (PhysMemWrite addrdesc 1 accdesc none data) ) : SailM PhysMemRetStatus )
      (pure (memstatus, addrdesc)))

def SPEResetSampleStorage (_ : Unit) : SailM Unit := do
  writeReg SPESampleContextEL1 (Zeros (n := 32))
  writeReg SPESampleContextEL1Valid false
  writeReg SPESampleContextEL2 (Zeros (n := 32))
  writeReg SPESampleContextEL2Valid false
  let loop_i_lower := 0
  let loop_i_upper := (SPEMaxCounters -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      writeReg SPESampleCounter (vectorUpdate (← readReg SPESampleCounter) i 0)
      writeReg SPESampleCounterValid (vectorUpdate (← readReg SPESampleCounterValid) i false)
      writeReg SPESampleCounterPending (vectorUpdate (← readReg SPESampleCounterPending) i false)
  (pure loop_vars)
  let loop_i_lower := 0
  let loop_i_upper := (SPEMaxAddrs -i 1)
  let mut loop_vars_1 := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      writeReg SPESampleAddressValid (vectorUpdate (← readReg SPESampleAddressValid) i false)
      writeReg SPESampleAddress (vectorUpdate (← readReg SPESampleAddress) i (Zeros (n := 64)))
  (pure loop_vars_1)
  writeReg SPESampleDataSource (Zeros (n := 16))
  writeReg SPESampleDataSourceValid false
  writeReg SPESampleClass (Zeros (n := 2))
  writeReg SPESampleSubclass (Zeros (n := 8))
  writeReg SPESampleSubclassValid false
  writeReg SPESampleTimestamp (Zeros (n := 64))
  writeReg SPESampleTimestampValid false
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange (← readReg SPESampleEvents) 63 48 (← (__IMPDEF_bits 16 "SPE EVENTS 63_48")))
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange (← readReg SPESampleEvents) 47 32 (Zeros (n := 16)))
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange (← readReg SPESampleEvents) 31 24 (← (__IMPDEF_bits 8 "SPE EVENTS 31_24")))
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange (← readReg SPESampleEvents) 23 16 (Zeros (n := 8)))
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange (← readReg SPESampleEvents) 15 12 (← (__IMPDEF_bits 4 "SPE EVENTS 15_12")))
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange (← readReg SPESampleEvents) 11 0 (Zeros (n := 12)))
  writeReg SPESampleInstIsNV2 false

def BRBEExceptionReturn (target_address_in : (BitVec 64)) (source_el : (BitVec 2)) : SailM Unit := SailME.run do
  let target_address : (BitVec 64) := target_address_in
  let questionMark := source_el
  if ((questionMark == EL3) : Bool)
  then
    (do
      if ((←((pure (! (← (HaveBRBEv1p1 ())))) <||> (do
           (pure ((_get_MDCR_EL3_Type_E3BREC (← readReg MDCR_EL3)) == (_get_MDCR_EL3_Type_E3BREW (← readReg MDCR_EL3))))))) : Bool)
      then SailME.throw (() : Unit)
      else (pure ()))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          if (((_get_BRBCR_EL2_Type_ERTN (← readReg BRBCR_EL2)) == 0#1) : Bool)
          then SailME.throw (() : Unit)
          else (pure ()))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              if (((_get_BRBCR_EL1_Type_ERTN (← readReg BRBCR_EL1)) == 0#1) : Bool)
              then SailME.throw (() : Unit)
              else (pure ()))
          else (pure ())))
  let source_valid ← (( do (BranchRecordAllowed source_el) ) : SailME Unit Bool )
  let target_valid ← (( do (BranchRecordAllowed (← readReg PSTATE).EL) ) : SailME Unit Bool )
  let branch_valid : Bool := (source_valid || target_valid)
  if (branch_valid : Bool)
  then
    (do
      let branch_type : (BitVec 6) := 0b000111#6
      let ccu ← (( do (undefined_bitvector 1) ) : SailME Unit (BitVec 1) )
      let cc ← (( do (undefined_bitvector 14) ) : SailME Unit (BitVec 14) )
      let (cc, ccu) ← (( do
        let (tup__0, tup__1) ← do (BranchEncCycleCount ())
        let ccu : (BitVec 1) := tup__0
        let cc : (BitVec 14) := tup__1
        (pure (cc, ccu)) ) : SailME Unit ((BitVec 14) × (BitVec 1)) )
      let lastfailed ← (( do
        if ((← (HaveTME ())) : Bool)
        then (pure (_get_BRBFCR_EL1_Type_LASTFAILED (← readReg BRBFCR_EL1)))
        else (pure 0#1) ) : SailME Unit (BitVec 1) )
      let transactional ← (( do
        if ((←((pure source_valid) <&&> (do
             (HaveTME ())) <&&> (do
             (pure ((← readReg TSTATE).depth >b 0))))) : Bool)
        then (pure 1#1)
        else (pure 0#1) ) : SailME Unit (BitVec 1) )
      let el ← (( do
        if (target_valid : Bool)
        then (pure (← readReg PSTATE).EL)
        else (pure 0b00#2) ) : SailME Unit (BitVec 2) )
      let mispredict ← (( do
        if (((←((pure source_valid) <&&> (do
               (BRBEMispredictAllowed ())))) && (BranchMispredict ())) : Bool)
        then (pure 1#1)
        else (pure 0#1) ) : SailME Unit (BitVec 1) )
      let sv : (BitVec 1) :=
        if (source_valid : Bool)
        then 1#1
        else 0#1
      let tv : (BitVec 1) :=
        if (target_valid : Bool)
        then 1#1
        else 0#1
      let source_address ← (( do
        if (source_valid : Bool)
        then (PC_read ())
        else (pure (Zeros (n := 64))) ) : SailME Unit (BitVec 64) )
      let target_address : (BitVec 64) :=
        if ((! target_valid) : Bool)
        then (Zeros (n := 64))
        else target_address
      (UpdateBranchRecordBuffer ccu cc lastfailed transactional branch_type el mispredict (sv +++ tv) source_address target_address)
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange (← readReg BRBFCR_EL1) 6 6 0#1)
      (PMUEvent PMU_EVENT_BRB_FILTRATE))
  else (pure ())
  writeReg __last_branch_valid branch_valid

def BRB_INJ (_ : Unit) : SailM Unit := do
  (UpdateBranchRecordBuffer (_get_BRBINFINJ_EL1_Type_CCU (← readReg BRBINFINJ_EL1)) (_get_BRBINFINJ_EL1_Type_CC (← readReg BRBINFINJ_EL1)) (_get_BRBINFINJ_EL1_Type_LASTFAILED (← readReg BRBINFINJ_EL1)) (_get_BRBINFINJ_EL1_Type_T (← readReg BRBINFINJ_EL1)) (_get_BRBINFINJ_EL1_Type_TYPE (← readReg BRBINFINJ_EL1)) (_get_BRBINFINJ_EL1_Type_EL (← readReg BRBINFINJ_EL1)) (_get_BRBINFINJ_EL1_Type_MPRED (← readReg BRBINFINJ_EL1)) (_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) (_get_BRBSRCINJ_EL1_Type_ADDRESS (← readReg BRBSRCINJ_EL1)) (_get_BRBTGTINJ_EL1_Type_ADDRESS (← readReg BRBTGTINJ_EL1)))
  writeReg BRBINFINJ_EL1 (Mk_BRBINFINJ_EL1_Type (← (__UNKNOWN_bits 64)))
  writeReg BRBSRCINJ_EL1 (Mk_BRBSRCINJ_EL1_Type (← (__UNKNOWN_bits 64)))
  writeReg BRBTGTINJ_EL1 (Mk_BRBTGTINJ_EL1_Type (← (__UNKNOWN_bits 64)))
  if ((← (ConstrainUnpredictableBool Unpredictable_BRBFILTRATE)) : Bool)
  then (PMUEvent PMU_EVENT_BRB_FILTRATE)
  else (pure ())

def BRB_IALL (_ : Unit) : SailM Unit := do
  let loop_i_lower := 0
  let loop_i_upper ← do (pure ((← (GetBRBENumRecords ())) -i 1))
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      sail_assert (i <b 64) "src/v8_base.sail:35655.39-35655.40"
      writeReg Records_SRC (vectorUpdate (← readReg Records_SRC) i (Mk_BRBSRCType (Zeros (n := 64))))
      writeReg Records_TGT (vectorUpdate (← readReg Records_TGT) i (Mk_BRBTGTType (Zeros (n := 64))))
      writeReg Records_INF (vectorUpdate (← readReg Records_INF) i (Mk_BRBINFType (Zeros (n := 64))))
  (pure loop_vars)

def DecodeRegExtend (op : (BitVec 3)) : SailM ExtendType := do
  match (op : BitVec 3) with
  | 0b000 => (pure ExtendType_UXTB)
  | 0b001 => (pure ExtendType_UXTH)
  | 0b010 => (pure ExtendType_UXTW)
  | 0b011 => (pure ExtendType_UXTX)
  | 0b100 => (pure ExtendType_SXTB)
  | 0b101 => (pure ExtendType_SXTH)
  | 0b110 => (pure ExtendType_SXTW)
  | 0b111 => (pure ExtendType_SXTX)
  | _ => (do (undefined_ExtendType ()))

def TLBI (r : TLBIRecord) (s : Shareability) : SailM Unit := do
  (report_tlbi r s)
  (pure (_TLBInvalidate ()))

def TLBIRange (regime : Regime) (Xt : (BitVec 64)) : SailM (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) := do
  let valid_name : Bool := true
  let start_address : (BitVec 64) := (Zeros (n := 64))
  let end_address_name : (BitVec 64) := (Zeros (n := 64))
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let tg_bits : Nat := 12
  if ((tg == 0b00#2) : Bool)
  then (pure (false, tg, start_address, end_address_name))
  else
    (do
      let (start_address, tg_bits) ← (( do
        match (tg : BitVec 2) with
        | 0b01 =>
          (do
            let tg_bits : Nat := 12
            let start_address ← (( do
              if ((← (HasLargeAddress regime)) : Bool)
              then
                (let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 52 16 (Sail.BitVec.extractLsb Xt 36 0))
                (pure (Sail.BitVec.updateSubrange start_address 63 53 (BitVec.replicateBits (BitVec.join1 [(BitVec.access Xt 36)]) 11))))
              else
                (let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 48 12 (Sail.BitVec.extractLsb Xt 36 0))
                (pure (Sail.BitVec.updateSubrange start_address 63 49 (BitVec.replicateBits (BitVec.join1 [(BitVec.access Xt 36)]) 15)))) ) : SailM (BitVec 64) )
            (pure (start_address, tg_bits)))
        | 0b10 =>
          (do
            let tg_bits : Nat := 14
            let start_address ← (( do
              if ((← (HasLargeAddress regime)) : Bool)
              then
                (let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 52 16 (Sail.BitVec.extractLsb Xt 36 0))
                (pure (Sail.BitVec.updateSubrange start_address 63 53 (BitVec.replicateBits (BitVec.join1 [(BitVec.access Xt 36)]) 11))))
              else
                (let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 50 14 (Sail.BitVec.extractLsb Xt 36 0))
                (pure (Sail.BitVec.updateSubrange start_address 63 51 (BitVec.replicateBits (BitVec.join1 [(BitVec.access Xt 36)]) 13)))) ) : SailM (BitVec 64) )
            (pure (start_address, tg_bits)))
        | 0b11 =>
          (let tg_bits : Nat := 16
          let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 52 16 (Sail.BitVec.extractLsb Xt 36 0))
          let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 63 53 (BitVec.replicateBits (BitVec.join1 [(BitVec.access Xt 36)]) 11))
          (pure (start_address, tg_bits)))
        | _ =>
          (do
            (Unreachable ())
            (pure (start_address, tg_bits))) ) : SailM ((BitVec 64) × Int) )
      let tg_bits := tg_bits
      let range := (Int.shiftl (num +i 1) (((5 *i scale) +i 1) +i tg_bits))
      let end_address_name : (BitVec 64) := (start_address + (integer_subrange range 63 0))
      let end_address_name : (BitVec 64) :=
        if (((BitVec.join1 [(BitVec.access end_address_name 52)]) != (BitVec.join1 [(BitVec.access start_address 52)])) : Bool)
        then ((BitVec.replicateBits (BitVec.join1 [(BitVec.access start_address 52)]) (64 -i 52)) +++ (Ones (n := 52)))
        else end_address_name
      (pure (valid_name, tg, start_address, end_address_name)))

def _set_DCZID_EL0_Type_BS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DCZID_EL0_Type_BS r v)

def _set_GMID_EL1_Type_BS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GMID_EL1_Type_BS r v)

def _set_DCZID_EL0_Type_DZP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DCZID_EL0_Type_DZP r v)

def _set_PRRR_Type_DS0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_DS0 r v)

def _set_PRRR_Type_DS1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_DS1 r v)

def _set_PRRR_Type_NOS0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_NOS0 r v)

def _set_PRRR_Type_NOS1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_NOS1 r v)

def _set_PRRR_Type_NOS2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_NOS2 r v)

def _set_PRRR_Type_NOS3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_NOS3 r v)

def _set_PRRR_Type_NOS4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_NOS4 r v)

def _set_PRRR_Type_NOS5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_NOS5 r v)

def _set_PRRR_Type_NOS6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_NOS6 r v)

def _set_PRRR_Type_NOS7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_NOS7 r v)

def _set_PRRR_Type_NS0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_NS0 r v)

def _set_CNTNSAR_Type_NS0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTNSAR_Type_NS0 r v)

def _set_PRRR_Type_NS1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_NS1 r v)

def _set_CNTNSAR_Type_NS1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTNSAR_Type_NS1 r v)

def _set_PRRR_Type_TR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_TR0 r v)

def _set_PRRR_Type_TR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_TR1 r v)

def _set_PRRR_Type_TR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_TR2 r v)

def _set_PRRR_Type_TR3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_TR3 r v)

def _set_PRRR_Type_TR4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_TR4 r v)

def _set_PRRR_Type_TR5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_TR5 r v)

def _set_PRRR_Type_TR6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_TR6 r v)

def _set_PRRR_Type_TR7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PRRR_Type_TR7 r v)

def _set_NMRR_Type_IR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_IR0 r v)

def _set_NMRR_Type_IR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_IR1 r v)

def _set_NMRR_Type_IR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_IR2 r v)

def _set_NMRR_Type_IR3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_IR3 r v)

def _set_NMRR_Type_IR4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_IR4 r v)

def _set_NMRR_Type_IR5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_IR5 r v)

def _set_NMRR_Type_IR6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_IR6 r v)

def _set_NMRR_Type_IR7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_IR7 r v)

def _set_NMRR_Type_OR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_OR0 r v)

def _set_NMRR_Type_OR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_OR1 r v)

def _set_NMRR_Type_OR2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_OR2 r v)

def _set_NMRR_Type_OR3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_OR3 r v)

def _set_NMRR_Type_OR4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_OR4 r v)

def _set_NMRR_Type_OR5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_OR5 r v)

def _set_NMRR_Type_OR6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_OR6 r v)

def _set_NMRR_Type_OR7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_NMRR_Type_OR7 r v)

def _set_DACR32_EL2_Type_D0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D0 r v)

def _set_DACR_Type_D0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D0 r v)

def _set_DACR32_EL2_Type_D1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D1 r v)

def _set_DACR_Type_D1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D1 r v)

def _set_DACR32_EL2_Type_D10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D10 r v)

def _set_DACR_Type_D10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D10 r v)

def _set_DACR32_EL2_Type_D11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D11 r v)

def _set_DACR_Type_D11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D11 r v)

def _set_DACR32_EL2_Type_D12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D12 r v)

def _set_DACR_Type_D12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D12 r v)

def _set_DACR32_EL2_Type_D13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D13 r v)

def _set_DACR_Type_D13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D13 r v)

def _set_DACR32_EL2_Type_D14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D14 r v)

def _set_DACR_Type_D14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D14 r v)

def _set_DACR32_EL2_Type_D15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D15 r v)

def _set_DACR_Type_D15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D15 r v)

def _set_DACR32_EL2_Type_D2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D2 r v)

def _set_DACR_Type_D2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D2 r v)

def _set_DACR32_EL2_Type_D3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D3 r v)

def _set_DACR_Type_D3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D3 r v)

def _set_DACR32_EL2_Type_D4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D4 r v)

def _set_DACR_Type_D4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D4 r v)

def _set_DACR32_EL2_Type_D5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D5 r v)

def _set_DACR_Type_D5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D5 r v)

def _set_DACR32_EL2_Type_D6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D6 r v)

def _set_DACR_Type_D6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D6 r v)

def _set_DACR32_EL2_Type_D7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D7 r v)

def _set_DACR_Type_D7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D7 r v)

def _set_DACR32_EL2_Type_D8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D8 r v)

def _set_DACR_Type_D8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D8 r v)

def _set_DACR32_EL2_Type_D9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR32_EL2_Type_D9 r v)

def _set_DACR_Type_D9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DACR_Type_D9 r v)

def _set_PAR_Type_ATTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_ATTR r v)

def _set_PAR_EL1_Type_ATTR (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_ATTR r v)

def _set_PAR_Type_FST (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_FST r v)

def _set_PAR_EL1_Type_FST (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_FST r v)

def _set_PAR_Type_FSTAGE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_FSTAGE r v)

def _set_PAR_Type_Inner (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_Inner r v)

def _set_PAR_Type_Outer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_Outer r v)

def _set_PAR_Type_S2WLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_Type_S2WLK r v)

def _set_PAR_EL1_Type_TopLevel (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PAR_EL1_Type_TopLevel r v)

def _set_CTILSR_Type_SLI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTILSR_Type_SLI r v)

def _set_EDLSR_Type_SLI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDLSR_Type_SLI r v)

def _set_PMLSR_Type_SLI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMLSR_Type_SLI r v)

def _set_CTILSR_Type_SLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTILSR_Type_SLK r v)

def _set_EDLSR_Type_SLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDLSR_Type_SLK r v)

def _set_PMLSR_Type_SLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMLSR_Type_SLK r v)

def _set_DBGDTR_EL0_Type_HighWord (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTR_EL0_Type_HighWord r v)

def _set_DBGDTR_EL0_Type_LowWord (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTR_EL0_Type_LowWord r v)

def _set_EDPRSR_Type_HALTED (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_HALTED r v)

def _set_EDPRSR_Type_PU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_PU r v)

def _set_EDPRSR_Type_R (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_R r v)

def _set_EDPRSR_Type_SDAD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_SDAD r v)

def _set_EDPRSR_Type_SDR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_SDR r v)

def _set_EDPRSR_Type_SPMAD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_SPMAD r v)

def _set_EDPRSR_Type_SR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRSR_Type_SR r v)

def _set_GICM_TYPER_Type_SR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_TYPER_Type_SR r v)

def _set_DBGDCCINT_Type_RX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDCCINT_Type_RX r v)

def _set_MDCCINT_EL1_Type_RX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCCINT_EL1_Type_RX r v)

def _set_DBGDCCINT_Type_TX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDCCINT_Type_TX r v)

def _set_MDCCINT_EL1_Type_TX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDCCINT_EL1_Type_TX r v)

def DCPSInstruction (target_el : (BitVec 2)) : SailM Unit := do
  let from_32 ← (( do (undefined_bool ()) ) : SailM Bool )
  let _ : Unit := (SynchronizeContext ())
  let handle_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let handle_el ← (( do
    let questionMark := target_el
    if ((questionMark == EL1) : Bool)
    then
      (do
        if ((←((pure ((← readReg PSTATE).EL == EL2)) <||> (do
             (pure ((← readReg PSTATE).EL == EL3)) <&&> (do
               (pure (! (← (UsingAArch32 ())))))))) : Bool)
        then (do (pure (← readReg PSTATE).EL))
        else
          (do
            if ((←((EL2Enabled ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure EL1)))
    else
      (do
        if ((questionMark == EL2) : Bool)
        then
          (do
            if ((! (HaveEL EL2)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else
              (do
                if ((←((pure ((← readReg PSTATE).EL == EL3)) <&&> (do
                     (pure (! (← (UsingAArch32 ()))))))) : Bool)
                then (pure EL3)
                else
                  (do
                    if ((←((pure (! (← (IsSecureEL2Enabled ())))) <&&> (do
                         (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
                    then sailThrow ((Error_Undefined ()))
                    else (pure EL2))))
        else
          (do
            if ((questionMark == EL3) : Bool)
            then
              (do
                if ((((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1) || (! (HaveEL EL3))) : Bool)
                then sailThrow ((Error_Undefined ()))
                else (pure EL3))
            else
              (do
                (Unreachable ())
                (pure handle_el)))) ) : SailM (BitVec 2) )
  let from_secure ← (( do (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure)) ) : SailM Bool )
  if ((← (ELUsingAArch32 handle_el)) : Bool)
  then
    (do
      if (((← readReg PSTATE).M == M32_Monitor) : Bool)
      then writeReg SCR (Sail.BitVec.updateSubrange (← readReg SCR) 0 0 0#1)
      else (pure ())
      sail_assert (← (UsingAArch32 ())) "src/v8_base.sail:39523.29-39523.30"
      let questionMark := handle_el
      if ((questionMark == EL1) : Bool)
      then
        (do
          (AArch32_WriteMode M32_Svc)
          if ((←((HavePANExt ()) <&&> (do
               (pure ((_get_SCTLR_Type_SPAN (← (SCTLR_read__2 ()))) == 0#1))))) : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with PAN := 1#1 }
          else (pure ()))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then (AArch32_WriteMode M32_Hyp)
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  (AArch32_WriteMode M32_Monitor)
                  if ((← (HavePANExt ())) : Bool)
                  then
                    (do
                      if ((! from_secure) : Bool)
                      then writeReg PSTATE { (← readReg PSTATE) with PAN := 0#1 }
                      else
                        (do
                          if (((_get_SCTLR_Type_SPAN (← (SCTLR_read__2 ()))) == 0#1) : Bool)
                          then writeReg PSTATE { (← readReg PSTATE) with PAN := 1#1 }
                          else (pure ())))
                  else (pure ()))
              else (pure ())))
      if ((handle_el == EL2) : Bool)
      then
        (do
          (ELR_hyp_write (← (__UNKNOWN_bits 32)))
          (HSR_write (Mk_HSR_Type (← (__UNKNOWN_bits 32)))))
      else (LR_write (← (__UNKNOWN_bits 32)))
      (SPSR_set (N := 32) (← (__UNKNOWN_bits 32)))
      writeReg PSTATE { (← readReg PSTATE) with E := ← (do (pure (_get_SCTLRType_EE (← (SCTLR_read__1 ()))))) }
      (DLR_write (← (__UNKNOWN_bits 32)))
      (DSPSR_write (Mk_DSPSR_Type (← (__UNKNOWN_bits 32)))))
  else
    (do
      let from_32 ← (( do (UsingAArch32 ()) ) : SailM Bool )
      if (from_32 : Bool)
      then (AArch64_MaybeZeroRegisterUppers ())
      else (pure ())
      if ((←((pure from_32) <&&> (do
           (HaveSME ())) <&&> (do
           (pure ((← readReg PSTATE).SM == 1#1))))) : Bool)
      then (ResetSVEState ())
      else (MaybeZeroSVEUppers target_el)
      writeReg PSTATE { (← readReg PSTATE) with nRW := 0#1 }
      writeReg PSTATE { (← readReg PSTATE) with SP := 1#1 }
      writeReg PSTATE { (← readReg PSTATE) with EL := handle_el }
      if ((←((HavePANExt ()) <&&> (do
           (pure (handle_el == EL1)) <&&> (do
             (pure ((_get_SCTLR_EL1_Type_SPAN (← readReg SCTLR_EL1)) == 0#1))) <||> (do
             (pure (handle_el == EL2)) <&&> (do
               (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))) <&&> (do
               (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))) <&&> (do
               (pure ((_get_SCTLR_EL2_Type_SPAN (← readReg SCTLR_EL2)) == 0#1))))))) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with PAN := 1#1 }
      else (pure ())
      (ELR_set__1 (← (__UNKNOWN_bits 64)))
      (SPSR_set (N := 64) (← (__UNKNOWN_bits 64)))
      (ESR_set__1 (Mk_ESRType (← (__UNKNOWN_bits 64))))
      writeReg DLR_EL0 (← (__UNKNOWN_bits 64))
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type (← (__UNKNOWN_bits 64)))
      if ((← (HaveUAOExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with UAO := 0#1 }
      else (pure ())
      if ((← (HaveMTEExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with TCO := 1#1 }
      else (pure ())
      if ((← (HaveGCS ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with EXLOCK := 0#1 }
      else (pure ()))
  (UpdateEDSCRFields ())
  let sync_errors ← (( do (HaveIESB ()) <&&> (do (pure ((_get_SCTLRType_IESB (← (SCTLR_read__1 ()))) == 1#1))) ) : SailM Bool )
  let sync_errors ← (( do
    if ((←((HaveDoubleFaultExt ()) <&&> (do
         (pure (! (← (UsingAArch32 ()))))))) : Bool)
    then (do (pure sync_errors) <||> (do (pure ((← (EffectiveEA ())) == 1#1)) <&&> (do (pure ((_get_SCR_EL3_Type_NMEA (← readReg SCR_EL3)) == 1#1))) <&&> (do (pure ((← readReg PSTATE).EL == EL3)))))
    else (pure sync_errors) ) : SailM Bool )
  let sync_errors ← (( do
    if ((! (← (ConstrainUnpredictableBool Unpredictable_IESBinDebug))) : Bool)
    then (pure false)
    else (pure sync_errors) ) : SailM Bool )
  let _ : Unit :=
    if (sync_errors : Bool)
    then (SynchronizeErrors ())
    else ()
  (pure ())

def CheckPendingResetCatch (_ : Unit) : SailM Unit := do
  if ((←((HaltingAllowed ()) <&&> (do
       (pure ((_get_EDESR_Type_RC (← readReg EDESR)) == 1#1))))) : Bool)
  then
    (do
      let is_async : Bool := true
      (Halt__1 DebugHalt_ResetCatch is_async))
  else (pure ())

def CheckResetCatch (_ : Unit) : SailM Unit := do
  if ((←((HaveDoPD ()) <&&> (do
       (pure ((_get_CTIDEVCTL_Type_RCE (← readReg CTIDEVCTL)) == 1#1))) <||> (do
       (pure (! (← (HaveDoPD ())))) <&&> (do
         (pure ((_get_EDECR_Type_RCE (← readReg EDECR)) == 1#1)))))) : Bool)
  then
    (do
      writeReg EDESR (Sail.BitVec.updateSubrange (← readReg EDESR) 1 1 1#1)
      if ((← (HaltingAllowed ())) : Bool)
      then (Halt DebugHalt_ResetCatch)
      else (pure ()))
  else (pure ())

def CheckPendingOSUnlockCatch (_ : Unit) : SailM Unit := do
  if ((←((HaltingAllowed ()) <&&> (do
       (pure ((_get_EDESR_Type_OSUC (← readReg EDESR)) == 1#1))))) : Bool)
  then
    (do
      let is_async : Bool := true
      (Halt__1 DebugHalt_OSUnlockCatch is_async))
  else (pure ())

def CheckOSUnlockCatch (_ : Unit) : SailM Unit := do
  if ((←((HaveDoPD ()) <&&> (do
       (pure ((_get_CTIDEVCTL_Type_OSUCE (← readReg CTIDEVCTL)) == 1#1))) <||> (do
       (pure (! (← (HaveDoPD ())))) <&&> (do
         (pure ((_get_EDECR_Type_OSUCE (← readReg EDECR)) == 1#1)))))) : Bool)
  then
    (do
      if ((! (← (Halted ()))) : Bool)
      then writeReg EDESR (Sail.BitVec.updateSubrange (← readReg EDESR) 0 0 1#1)
      else (pure ()))
  else (pure ())

def _set_EDVIDSR_Type_CONTEXTIDR_EL2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDVIDSR_Type_CONTEXTIDR_EL2 r v)

def _set_EDVIDSR_Type_HV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDVIDSR_Type_HV r v)

def _set_PMPCSR_Type_PCSample (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 56)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPCSR_Type_PCSample r v)

def _set_DBGDEVID_Type_PCSample (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID_Type_PCSample r v)

def _set_EDDEVID_Type_PCSample (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVID_Type_PCSample r v)

def _set_PMDEVID_Type_PCSample (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMDEVID_Type_PCSample r v)

def _set_HTRFCR_Type_E0HTRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTRFCR_Type_E0HTRE r v)

def _set_TRFCR_EL2_Type_E0HTRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_EL2_Type_E0HTRE r v)

def _set_HTRFCR_Type_E2TRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HTRFCR_Type_E2TRE r v)

def _set_TRFCR_EL2_Type_E2TRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_EL2_Type_E2TRE r v)

def _set_TRFCR_EL1_Type_E0TRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_EL1_Type_E0TRE r v)

def _set_TRFCR_Type_E0TRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_Type_E0TRE r v)

def _set_TRFCR_EL1_Type_E1TRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_EL1_Type_E1TRE r v)

def _set_TRFCR_Type_E1TRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TRFCR_Type_E1TRE r v)

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV82 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap2_IMPLEMENTED enabled
  if (enabled : Bool)
  then (__ConfigureV81 enabled)
  else (pure ())

def _set_DBGVCR32_EL2_Type_NSD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSD r v)

def _set_DBGVCR_Type_NSD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_NSD r v)

def _set_DBGVCR32_EL2_Type_NSF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSF r v)

def _set_DBGVCR_Type_NSF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_NSF r v)

def _set_DBGVCR32_EL2_Type_NSI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSI r v)

def _set_DBGVCR_Type_NSI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_NSI r v)

def _set_DBGVCR32_EL2_Type_NSP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSP r v)

def _set_DBGVCR_Type_NSP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_NSP r v)

def _set_DBGVCR32_EL2_Type_NSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_NSS r v)

def _set_DBGVCR_Type_NSS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_NSS r v)

def _set_DBGVCR32_EL2_Type_SD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SD r v)

def _set_DBGVCR_Type_SD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_SD r v)

def _set_DBGVCR32_EL2_Type_SF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SF r v)

def _set_DBGVCR_Type_SF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_SF r v)

def _set_DBGVCR32_EL2_Type_SI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SI r v)

def _set_DBGVCR_Type_SI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_SI r v)

def _set_DBGVCR32_EL2_Type_SP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SP r v)

def _set_DBGVCR_Type_SP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_SP r v)

def _set_DBGVCR32_EL2_Type_SU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_SU r v)

def _set_DBGVCR_Type_SU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_SU r v)

def _set_DBGVCR_Type_MD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_MD r v)

def _set_DBGVCR_Type_MF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_MF r v)

def _set_DBGVCR_Type_MI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_MI r v)

def _set_DBGVCR_Type_MP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_MP r v)

def _set_DBGVCR_Type_MS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGVCR_Type_MS r v)

/-- Type quantifiers: k_N : Nat, amount : Int, k_N ≥ 0 -/
def Shift_C (value_name : (BitVec k_N)) (srtype : SRType) (amount : Int) (carry_in : (BitVec 1)) : SailM ((BitVec k_N) × (BitVec 1)) := do
  sail_assert (! ((BEq.beq srtype SRType_RRX) && (amount != 1))) "src/v8_base.sail:41274.55-41274.56"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length value_name)) ) : SailM (BitVec k_N) )
  let carry_out ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (carry_out, result) ← (( do
    if ((amount == 0) : Bool)
    then
      (let (tup__0, tup__1) := ((value_name, carry_in) : ((BitVec k_N) × (BitVec 1)))
      let result : (BitVec k_N) := tup__0
      let carry_out : (BitVec 1) := tup__1
      (pure (carry_out, result)))
    else
      (do
        let (carry_out, result) ← (( do
          match srtype with
          | .SRType_LSL =>
            (let (tup__0, tup__1) := ((LSL_C value_name amount) : ((BitVec k_N) × (BitVec 1)))
            let result : (BitVec k_N) := tup__0
            let carry_out : (BitVec 1) := tup__1
            (pure (carry_out, result)))
          | .SRType_LSR =>
            (let (tup__0, tup__1) := ((LSR_C value_name amount) : ((BitVec k_N) × (BitVec 1)))
            let result : (BitVec k_N) := tup__0
            let carry_out : (BitVec 1) := tup__1
            (pure (carry_out, result)))
          | .SRType_ASR =>
            (do
              sail_assert (((Sail.BitVec.length value_name) ≥b 0) && (amount ≥b 0)) "src/v8_base.sail:41288.57-41288.58"
              let (tup__0, tup__1) := ((ASR_C value_name amount) : ((BitVec k_N) × (BitVec 1)))
              let result : (BitVec k_N) := tup__0
              let carry_out : (BitVec 1) := tup__1
              (pure (carry_out, result)))
          | .SRType_ROR =>
            (do
              sail_assert ((Sail.BitVec.length value_name) >b 0) "src/v8_base.sail:41292.39-41292.40"
              let (tup__0, tup__1) ← do (ROR_C value_name amount)
              let result : (BitVec k_N) := tup__0
              let carry_out : (BitVec 1) := tup__1
              (pure (carry_out, result)))
          | .SRType_RRX =>
            (do
              sail_assert ((Sail.BitVec.length value_name) >b 1) "src/v8_base.sail:41296.39-41296.40"
              let (tup__0, tup__1) := ((RRX_C value_name carry_in) : ((BitVec k_N) × (BitVec 1)))
              let result : (BitVec k_N) := tup__0
              let carry_out : (BitVec 1) := tup__1
              (pure (carry_out, result))) ) : SailM ((BitVec 1) × (BitVec k_N)) )
        (pure (carry_out, result))) ) : SailM ((BitVec 1) × (BitVec k_N)) )
  (pure (result, carry_out))

def DecodeImmShift (srtype : (BitVec 2)) (imm5 : (BitVec 5)) : SailM (SRType × Int) := do
  let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
  let shift_n ← (( do (undefined_range 0 32) ) : SailM Nat )
  let (shift_n, shift_t) : (Nat × SRType) :=
    match (srtype : BitVec 2) with
    | 0b00 =>
      (let shift_t : SRType := SRType_LSL
      let shift_n : Nat := (BitVec.toNat imm5)
      (shift_n, shift_t))
    | 0b01 =>
      (let shift_t : SRType := SRType_LSR
      let shift_n : Nat :=
        if ((imm5 == 0b00000#5) : Bool)
        then 32
        else (BitVec.toNat imm5)
      (shift_n, shift_t))
    | 0b10 =>
      (let shift_t : SRType := SRType_ASR
      let shift_n : Nat :=
        if ((imm5 == 0b00000#5) : Bool)
        then 32
        else (BitVec.toNat imm5)
      (shift_n, shift_t))
    | _ =>
      (let (shift_n, shift_t) : (Nat × SRType) :=
        if ((imm5 == 0b00000#5) : Bool)
        then
          (let shift_t : SRType := SRType_RRX
          let shift_n : Nat := 1
          (shift_n, shift_t))
        else
          (let shift_t : SRType := SRType_ROR
          let shift_n : Nat := (BitVec.toNat imm5)
          (shift_n, shift_t))
      (shift_n, shift_t))
  let shift_n := shift_n
  (pure (shift_t, shift_n))

def DecodeRegShift (srtype : (BitVec 2)) : SailM SRType := do
  let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
  match (srtype : BitVec 2) with
  | 0b00 => (pure SRType_LSL)
  | 0b01 => (pure SRType_LSR)
  | 0b10 => (pure SRType_ASR)
  | _ => (pure SRType_ROR)

def T32ExpandImm (imm12 : (BitVec 12)) : SailM (BitVec 32) := do
  let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (__tup_0, _) ← do (T32ExpandImm_C imm12 (← readReg PSTATE).C)
  (pure __tup_0)

/-- Type quantifiers: n : Int -/
def D_read (n : Int) : SailM (BitVec 64) := do
  sail_assert ((n ≥b 0) && (n ≤b 31)) "src/v8_base.sail:41714.27-41714.28"
  let base := ((Nat.mod n 2) *i 64)
  let vreg ← (( do (V_read (Int.ediv n 2) 128) ) : SailM (BitVec 128) )
  (pure (Sail.BitVec.extractLsb vreg (base +i 63) base))

def StandardFPSCRValue (_ : Unit) : SailM (BitVec 64) := do
  let value_name ← (( do (pure ((((0b00000#5 +++ (_get_FPSCR_Type_AHP (← (FPSCR_read__1 ())))) +++ 0b110000#6) +++ (_get_FPSCR_Type_FZ16 (← (FPSCR_read__1 ())))) +++ 0b0000000000000000000#19)) ) : SailM (BitVec 32) )
  (pure (Mk_FPCRType (Sail.BitVec.zeroExtend value_name 64)))

/-- Type quantifiers: k_aligned : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def AArch32_MemSingle_set (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) (aligned : Bool) (value_name : (BitVec (size * 8))) : SailM Unit := do
  let ispair : Bool := false
  (AArch32_MemSingle_set__1 address size accdesc aligned ispair value_name)

/-- Type quantifiers: k_ispair : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def Mem_with_type_read__1 (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) (ispair : Bool) : SailM (BitVec (size * 8)) := do
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  sail_assert ((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16))))) "src/v8_base.sail:41981.69-41981.70"
  let halfsize := (Int.ediv size 2)
  let value_name ← (( do (undefined_bitvector (size *i 8)) ) : SailM (BitVec (size * 8)) )
  let alignment :=
    if (ispair : Bool)
    then halfsize
    else size
  let aligned : Bool := (IsAligned__1 address alignment)
  if ((←((pure (! aligned)) <&&> (do
       (AArch32_UnalignedAccessFaults accdesc)))) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let value_name ← (( do
    if (aligned : Bool)
    then (do (AArch32_MemSingle_read__1 address size accdesc aligned ispair))
    else
      (do
        sail_assert (size >b 1) "src/v8_base.sail:41992.23-41992.24"
        let value_name ← (pure (Sail.BitVec.updateSubrange value_name 7 0 (← (AArch32_MemSingle_read address 1 accdesc aligned))))
        let c ← (( do (ConstrainUnpredictable Unpredictable_DEVPAGE2) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_FAULT) || (BEq.beq c Constraint_NONE)) "src/v8_base.sail:41995.59-41995.60"
        let aligned : Bool :=
          if ((BEq.beq c Constraint_NONE) : Bool)
          then true
          else aligned
        let loop_i_lower := 1
        let loop_i_upper := (size -i 1)
        let mut loop_vars := value_name
        for i in [loop_i_lower:loop_i_upper:1]i do
          let value_name := loop_vars
          loop_vars ← do (pure (Sail.BitVec.updateSubrange value_name ((8 *i i) +i 7) (8 *i i) (← (AArch32_MemSingle_read (BitVec.addInt address i) 1 accdesc aligned))))
        (pure loop_vars)) ) : SailM (BitVec (size * 8)) )
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then (pure (reverse_endianness value_name))
  else (pure value_name)

/-- Type quantifiers: size : Int -/
def AArch32_SetExclusiveMonitors (address : (BitVec 32)) (size : Int) : SailM Unit := do
  writeReg __ExclusiveMonitorSet true
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_LOAD acqrel tagchecked) ) : SailM AccessDescriptor )
  let aligned : Bool := (IsAligned__1 address size)
  if ((! aligned) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let memaddrdesc ← (( do (AArch32_TranslateAddress address accdesc aligned size) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then (pure ())
  else
    (let _ : Unit :=
      if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
      then (MarkExclusiveGlobal memaddrdesc.paddress (ProcessorID ()) size)
      else ()
    let _ : Unit := (MarkExclusiveLocal memaddrdesc.paddress (ProcessorID ()) size)
    (pure (AArch32_MarkExclusiveVA address (ProcessorID ()) size)))

/-- Type quantifiers: size : Int -/
def AArch32_ExclusiveMonitorsPass (address : (BitVec 32)) (size : Int) : SailM Bool := do
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_STORE acqrel tagchecked) ) : SailM AccessDescriptor )
  let aligned : Bool := (IsAligned__1 address size)
  if ((! aligned) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  if ((! (← (AArch32_IsExclusiveVA address (ProcessorID ()) size))) : Bool)
  then (pure false)
  else
    (do
      let memaddrdesc ← (( do (AArch32_TranslateAddress address accdesc aligned size) ) : SailM AddressDescriptor )
      if ((IsFault memaddrdesc) : Bool)
      then (AArch32_Abort address memaddrdesc.fault)
      else (pure ())
      let passed : Bool := (IsExclusiveLocal memaddrdesc.paddress (ProcessorID ()) size)
      let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
      if ((passed && (bne memaddrdesc.memattrs.shareability Shareability_NSH)) : Bool)
      then (pure (IsExclusiveGlobal memaddrdesc.paddress (ProcessorID ()) size))
      else (pure passed))

/-- Type quantifiers: n : Int -/
def S_read (n : Int) : SailM (BitVec 32) := do
  sail_assert ((n ≥b 0) && (n ≤b 31)) "src/v8_base.sail:42210.27-42210.28"
  let base := ((Nat.mod n 4) *i 32)
  let vreg ← (( do (V_read (Int.ediv n 4) 128) ) : SailM (BitVec 128) )
  (pure (Sail.BitVec.extractLsb vreg (base +i 31) base))

/-- Type quantifiers: n : Int -/
def S_set (n : Int) (value_name : (BitVec 32)) : SailM Unit := do
  sail_assert ((n ≥b 0) && (n ≤b 31)) "src/v8_base.sail:42219.27-42219.28"
  let base := ((Nat.mod n 4) *i 32)
  let vreg ← (( do (V_read (Int.ediv n 4) 128) ) : SailM (BitVec 128) )
  let vreg : (BitVec 128) := (Sail.BitVec.updateSubrange vreg (base +i 31) base value_name)
  (V_set (Int.ediv n 4) 128 vreg)

/-- Type quantifiers: n : Int -/
def D_set (n : Int) (value_name : (BitVec 64)) : SailM Unit := do
  sail_assert ((n ≥b 0) && (n ≤b 31)) "src/v8_base.sail:42230.27-42230.28"
  let base := ((Nat.mod n 2) *i 64)
  let vreg ← (( do (V_read (Int.ediv n 2) 128) ) : SailM (BitVec 128) )
  let vreg : (BitVec 128) := (Sail.BitVec.updateSubrange vreg (base +i 63) base value_name)
  (V_set (Int.ediv n 2) 128 vreg)

/-- Type quantifiers: n : Int -/
def Q_read (n : Int) : SailM (BitVec 128) := do
  sail_assert ((n ≥b 0) && (n ≤b 15)) "src/v8_base.sail:42241.27-42241.28"
  (V_read n 128)

def AArch32_ResetSIMDFPRegisters (_ : Unit) : SailM Unit := do
  let loop_i_lower := 0
  let loop_i_upper := 15
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do (Q_set i (← (__UNKNOWN_bits 128)))
  (pure loop_vars)

def AArch32_ResetSpecialRegisters (_ : Unit) : SailM Unit := do
  writeReg SPSR_fiq (Sail.BitVec.updateSubrange (← readReg SPSR_fiq) 31 0 (← (__UNKNOWN_bits 32)))
  writeReg SPSR_irq (Sail.BitVec.updateSubrange (← readReg SPSR_irq) 31 0 (← (__UNKNOWN_bits 32)))
  (SPSR_svc_write (Mk_SPSR_svc_Type (Sail.BitVec.updateSubrange (← (SPSR_svc_read ())) 31 0 (← (__UNKNOWN_bits 32)))))
  writeReg SPSR_abt (Sail.BitVec.updateSubrange (← readReg SPSR_abt) 31 0 (← (__UNKNOWN_bits 32)))
  writeReg SPSR_und (Sail.BitVec.updateSubrange (← readReg SPSR_und) 31 0 (← (__UNKNOWN_bits 32)))
  if ((HaveEL EL2) : Bool)
  then
    (do
      (SPSR_hyp_write (Mk_SPSR_hyp_Type (← (__UNKNOWN_bits 32))))
      (ELR_hyp_write (← (__UNKNOWN_bits 32))))
  else (pure ())
  if ((HaveEL EL3) : Bool)
  then writeReg SPSR_mon (Mk_SPSR_mon_Type (← (__UNKNOWN_bits 32)))
  else (pure ())
  (DLR_write (← (__UNKNOWN_bits 32)))
  (DSPSR_write (Mk_DSPSR_Type (← (__UNKNOWN_bits 32))))

def BXWritePC (address_in : (BitVec 32)) (branch_type : BranchType) : SailM Unit := do
  let address : (BitVec 32) := address_in
  let address ← (( do
    if (((BitVec.join1 [(BitVec.access address 0)]) == 1#1) : Bool)
    then
      (do
        (SelectInstrSet InstrSet_T32)
        (pure (BitVec.update address 0 (Bit 0#1))))
    else
      (do
        (SelectInstrSet InstrSet_A32)
        if ((←((pure ((BitVec.join1 [(BitVec.access address 1)]) == 1#1)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_A32FORCEALIGNPC)))) : Bool)
        then (pure (BitVec.update address 1 (Bit 0#1)))
        else (pure address)) ) : SailM (BitVec 32) )
  let branch_conditional ← (( do
    (pure (! (← (do
          let b__0 ← do (AArch32_CurrentCond ())
          if (((Sail.BitVec.extractLsb b__0 3 1) == (0b111#3 : (BitVec 3))) : Bool)
          then (pure true)
          else (pure false))))) ) : SailM Bool )
  (BranchTo address branch_type branch_conditional)

def BranchWritePC (address_in : (BitVec 32)) (branch_type : BranchType) : SailM Unit := do
  let address : (BitVec 32) := address_in
  let address ← (( do
    if ((BEq.beq (← (CurrentInstrSet ())) InstrSet_A32) : Bool)
    then (pure (Sail.BitVec.updateSubrange address 1 0 0b00#2))
    else (pure (BitVec.update address 0 (Bit 0#1))) ) : SailM (BitVec 32) )
  let branch_conditional ← (( do
    (pure (! (← (do
          let b__0 ← do (AArch32_CurrentCond ())
          if (((Sail.BitVec.extractLsb b__0 3 1) == (0b111#3 : (BitVec 3))) : Bool)
          then (pure true)
          else (pure false))))) ) : SailM Bool )
  (BranchTo address branch_type branch_conditional)

/-- Type quantifiers: n : Int -/
def Qin_read (n : Int) : SailM (BitVec 128) := do
  sail_assert ((n ≥b 0) && (n ≤b 15)) "src/v8_base.sail:42446.27-42446.28"
  (pure ((← (Din_read ((2 *i n) +i 1))) +++ (← (Din_read (2 *i n)))))

def ConditionPassed (_ : Unit) : SailM Bool := do
  (ConditionHolds (← (AArch32_CurrentCond ())))

def CPSRWriteByInstr (value_name : (BitVec 32)) (bytemask : (BitVec 4)) : SailM Unit := do
  let privileged ← (( do (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  if (((BitVec.join1 [(BitVec.access bytemask 3)]) == 1#1) : Bool)
  then
    (do
      let split_vec := (Sail.BitVec.extractLsb value_name 31 27)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 4 4) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with Q := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  if (((BitVec.join1 [(BitVec.access bytemask 2)]) == 1#1) : Bool)
  then
    (do
      if ((← (HaveSSBSExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with SSBS := (BitVec.join1 [(BitVec.access value_name 23)]) }
      else (pure ())
      if (privileged : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with PAN := (BitVec.join1 [(BitVec.access value_name 22)]) }
      else (pure ())
      if ((← (HaveDITExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with DIT := (BitVec.join1 [(BitVec.access value_name 21)]) }
      else (pure ())
      writeReg PSTATE { (← readReg PSTATE) with GE := (Sail.BitVec.extractLsb value_name 19 16) })
  else (pure ())
  if (((BitVec.join1 [(BitVec.access bytemask 1)]) == 1#1) : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with E := (BitVec.join1 [(BitVec.access value_name 9)]) }
      if (privileged : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with A := (BitVec.join1 [(BitVec.access value_name 8)]) }
      else (pure ()))
  else (pure ())
  if (((BitVec.join1 [(BitVec.access bytemask 0)]) == 1#1) : Bool)
  then
    (do
      if (privileged : Bool)
      then
        (do
          let split_vec := (Sail.BitVec.extractLsb value_name 7 6)
          writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb split_vec 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb split_vec 0 0) }
          (AArch32_WriteModeByInstr (Sail.BitVec.extractLsb value_name 4 0)))
      else (pure ()))
  else (pure ())

def SPSRWriteByInstr (value_name : (BitVec 32)) (bytemask : (BitVec 4)) : SailM Unit := do
  let new_spsr ← (( do (SPSR_read (N := 32)) ) : SailM (BitVec 32) )
  let new_spsr : (BitVec 32) :=
    if (((BitVec.join1 [(BitVec.access bytemask 3)]) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 31 24 (Sail.BitVec.extractLsb value_name 31 24))
    else new_spsr
  let new_spsr : (BitVec 32) :=
    if (((BitVec.join1 [(BitVec.access bytemask 2)]) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 23 16 (Sail.BitVec.extractLsb value_name 23 16))
    else new_spsr
  let new_spsr : (BitVec 32) :=
    if (((BitVec.join1 [(BitVec.access bytemask 1)]) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 15 8 (Sail.BitVec.extractLsb value_name 15 8))
    else new_spsr
  let new_spsr : (BitVec 32) :=
    if (((BitVec.join1 [(BitVec.access bytemask 0)]) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 7 0 (Sail.BitVec.extractLsb value_name 7 0))
    else new_spsr
  (SPSR_set (N := 32) new_spsr)

/-- Type quantifiers: N : Nat, i : Int, 0 ≤ (N - 1) -/
def UnsignedSat (i : Int) (N : Nat) : SailM (BitVec N) := do
  let result ← (( do (undefined_bitvector N) ) : SailM (BitVec N) )
  let (__tup_0, _) ← do (UnsignedSatQ i N)
  (pure __tup_0)

/-- Type quantifiers: N : Nat, i : Int, 0 ≤ (N - 1) -/
def SignedSat (i : Int) (N : Nat) : SailM (BitVec N) := do
  let result ← (( do (undefined_bitvector N) ) : SailM (BitVec N) )
  let (__tup_0, _) ← do (SignedSatQ i N)
  (pure __tup_0)

def AArch32_TakeSMCException (_ : Unit) : SailM Unit := do
  sail_assert (←((pure (HaveEL EL3)) <&&> (do
    (ELUsingAArch32 EL3)))) "src/v8_base.sail:42900.44-42900.45"
  (AArch32_ITAdvance ())
  (SSAdvance ())
  let preferred_exception_return ← (( do (NextInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset := (BitVec.toNat 0x08#8)
  let lr_offset := 0
  (AArch32_EnterMonitorMode preferred_exception_return lr_offset vect_offset)

def AArch32_TakeHVCException (immediate : (BitVec 16)) : SailM Unit := do
  sail_assert (←((pure (HaveEL EL2)) <&&> (do
    (ELUsingAArch32 EL2)))) "src/v8_base.sail:42912.44-42912.45"
  (AArch32_ITAdvance ())
  (SSAdvance ())
  let preferred_exception_return ← (( do (NextInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset := (BitVec.toNat 0x08#8)
  let except ← (( do (ExceptionSyndrome Exception_HypervisorCall) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (AArch32_EnterHypMode except preferred_exception_return vect_offset)
  else (AArch32_EnterHypMode except preferred_exception_return (BitVec.toNat 0x14#8))

def AArch32_TakeSVCException (immediate : (BitVec 16)) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  (AArch32_ITAdvance ())
  (SSAdvance ())
  let route_to_hyp ← (( do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1))) ) : SailM Bool )
  let preferred_exception_return ← (( do (NextInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset := (BitVec.toNat 0x08#8)
  let lr_offset := 0
  if ((((← readReg PSTATE).EL == EL2) || route_to_hyp) : Bool)
  then
    (do
      let except ← (( do (ExceptionSyndrome Exception_SupervisorCall) ) : SailM ExceptionRecord )
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
      if (((← readReg PSTATE).EL == EL2) : Bool)
      then (AArch32_EnterHypMode except preferred_exception_return vect_offset)
      else (AArch32_EnterHypMode except preferred_exception_return (BitVec.toNat 0x14#8)))
  else (AArch32_EnterMode M32_Svc preferred_exception_return lr_offset vect_offset)

def AArch32_UndefinedFault (_ : Unit) : SailM Unit := do
  if ((← (AArch32_GeneralExceptionsToAArch64 ())) : Bool)
  then (AArch64_UndefinedFault ())
  else (pure ())
  (AArch32_TakeUndefInstrException ())

def AArch32_CheckForSVCTrap (immediate : (BitVec 16)) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  let route_to_el2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let vect_offset ← (( do (undefined_int ()) ) : SailM Int )
  let route_to_el2 ← (( do
    if ((← (HaveFGTExt ())) : Bool)
    then
      (do
        let route_to_el2 : Bool := false
        let route_to_el2 ← (( do
          if (((← readReg PSTATE).EL == EL0) : Bool)
          then (do (pure (! (← (ELUsingAArch32 EL1)))) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HFGITR_EL2_Type_SVC_EL0 (← readReg HFGITR_EL2)) == 1#1))) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) != 0b11#2)) <&&> (do (pure (! (HaveEL EL3))) <||> (do (pure ((_get_SCR_EL3_Type_FGTEn (← readReg SCR_EL3)) == 1#1))))))
          else (pure route_to_el2) ) : SailM Bool )
        if (route_to_el2 : Bool)
        then
          (do
            let except ← (( do (ExceptionSyndrome Exception_SupervisorCall) ) : SailM ExceptionRecord )
            let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
            let except : ExceptionRecord := { except with trappedsyscallinst := true }
            let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
            let vect_offset := (BitVec.toNat 0x0#4)
            (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
        else (pure ())
        (pure route_to_el2))
    else (pure route_to_el2) ) : SailM Bool )
  let route_to_el2 := route_to_el2
  (pure ())

def AArch32_CheckForSMCUndefOrTrap (_ : Unit) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  let route_to_hyp ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((←((pure (! (HaveEL EL3))) <||> (do
       (pure ((← readReg PSTATE).EL == EL0))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((EL2Enabled ()) <&&> (do
       (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
  then (AArch64_CheckForSMCUndefOrTrap (Zeros (n := 16)))
  else
    (do
      let route_to_hyp ← (( do (EL2Enabled ()) <&&> (do (pure ((← readReg PSTATE).EL == EL1))) <&&> (do (pure ((_get_HCR_Type_TSC (← (HCR_read ()))) == 1#1))) ) : SailM Bool )
      if (route_to_hyp : Bool)
      then
        (do
          let except ← (( do (ExceptionSyndrome Exception_MonitorCall) ) : SailM ExceptionRecord )
          (AArch32_TakeHypTrapException__1 except))
      else (pure ()))

def AArch32_CheckITEnabled (mask : (BitVec 4)) : SailM Unit := do
  let accdesc ← (( do (undefined_AccessDescriptor ()) ) : SailM AccessDescriptor )
  let aligned ← (( do (undefined_bool ()) ) : SailM Bool )
  let next_instr ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  let it_disabled ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let it_disabled ← (( do
    if (((← readReg PSTATE).EL == EL2) : Bool)
    then (do (pure (_get_HSCTLR_Type_ITD (← (HSCTLR_read ())))))
    else
      (do
        if ((← (ELUsingAArch32 EL1)) : Bool)
        then (pure (_get_SCTLR_Type_ITD (← (SCTLR_read__2 ()))))
        else (pure (_get_SCTLRType_ITD (← (SCTLR_read__1 ()))))) ) : SailM (BitVec 1) )
  if ((it_disabled == 1#1) : Bool)
  then
    (do
      if ((mask != 0b1000#4) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let accdesc ← (( do (CreateAccDescIFetch ()) ) : SailM AccessDescriptor )
      let aligned : Bool := true
      let next_instr ← (( do (AArch32_MemSingle_read (← (NextInstrAddr 32)) 2 accdesc aligned) ) : SailM (BitVec 16) )
      if ((let b__0 := next_instr
         if (((Sail.BitVec.extractLsb b__0 15 14) == (0b11#2 : (BitVec 2))) : Bool)
         then true
         else
           (if (((Sail.BitVec.extractLsb b__0 15 12) == (0xB#4 : (BitVec 4))) : Bool)
           then true
           else
             (if (((Sail.BitVec.extractLsb b__0 15 11) == (0b10100#5 : (BitVec 5))) : Bool)
             then true
             else
               (if (((Sail.BitVec.extractLsb b__0 15 11) == (0b01001#5 : (BitVec 5))) : Bool)
               then true
               else
                 (if ((((Sail.BitVec.extractLsb b__0 15 10) == (0b010001#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb b__0 6 3) == (0xF#4 : (BitVec 4)))) : Bool)
                 then true
                 else
                   (if ((((Sail.BitVec.extractLsb b__0 15 10) == (0b010001#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb b__0 7 7) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 2 0) == (0b111#3 : (BitVec 3))))) : Bool)
                   then true
                   else false))))) : Bool) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ()))
  else (pure ())

def AArch32_CheckSETENDEnabled (_ : Unit) : SailM Unit := do
  let setend_disabled ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let setend_disabled ← (( do
    if (((← readReg PSTATE).EL == EL2) : Bool)
    then (do (pure (_get_HSCTLR_Type_SED (← (HSCTLR_read ())))))
    else
      (do
        if ((← (ELUsingAArch32 EL1)) : Bool)
        then (pure (_get_SCTLR_Type_SED (← (SCTLR_read__2 ()))))
        else (pure (_get_SCTLRType_SED (← (SCTLR_read__1 ()))))) ) : SailM (BitVec 1) )
  if ((setend_disabled == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let setend_disabled := setend_disabled
  (pure ())

def AArch32_SoftwareBreakpoint (immediate : (BitVec 16)) : SailM Unit := do
  if ((←((EL2Enabled ()) <&&> (do
       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do
         (pure ((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) == 1#1)))) <||> (do
       (pure (! (← (ELUsingAArch32 EL1))))))) : Bool)
  then (AArch64_SoftwareBreakpoint immediate)
  else (pure ())
  let accdesc ← (( do (CreateAccDescIFetch ()) ) : SailM AccessDescriptor )
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let vaddress ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  let fault : FaultRecord := { fault with statuscode := Fault_Debug }
  let fault : FaultRecord := { fault with debugmoe := DebugException_BKPT }
  (AArch32_Abort vaddress fault)


