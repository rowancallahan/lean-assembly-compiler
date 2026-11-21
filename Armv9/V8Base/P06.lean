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
import Armv9.V8Base.P03
import Armv9.V8Base.P04
import Armv9.V8Base.P05

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

def AArch32_PMUSwIncrement (sw_incr : (BitVec 32)) : SailM Unit := do
  if ((←((pure ((_get_PMCR_Type_E (← (PMCR_read ()))) == 0#1)) <&&> (do
       (pure ((_get_HDCR_Type_HPME (← (HDCR_read ()))) == 0#1))))) : Bool)
  then (pure ())
  else
    (do
      let counters ← do (AArch32_GetNumEventCountersAccessible ())
      if ((counters != 0) : Bool)
      then
        (do
          let loop_idx_lower := 0
          let loop_idx_upper := (counters -i 1)
          let mut loop_vars := ()
          for idx in [loop_idx_lower:loop_idx_upper:1]i do
            let () := loop_vars
            loop_vars ← do
              sail_assert ((0 ≤b idx) && (idx <b 32)) "src/v8_base.sail:43529.64-43529.65"
              if (((BitVec.join1 [(BitVec.access sw_incr idx)]) == 1#1) : Bool)
              then (PMUEvent__2 PMU_EVENT_SW_INCR 1 idx)
              else (pure ())
          (pure loop_vars))
      else (pure ()))

def _set_ID_MMFR2_EL1_Type_HWAccFlg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_HWAccFlg r v)

def _set_ID_MMFR2_Type_HWAccFlg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_Type_HWAccFlg r v)

def _set_ID_MMFR2_EL1_Type_HvdTLB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_HvdTLB r v)

def _set_ID_MMFR2_Type_HvdTLB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_Type_HvdTLB r v)

def _set_ID_MMFR2_EL1_Type_L1HvdBG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_L1HvdBG r v)

def _set_ID_MMFR2_Type_L1HvdBG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_Type_L1HvdBG r v)

def _set_ID_MMFR2_EL1_Type_L1HvdFG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_L1HvdFG r v)

def _set_ID_MMFR2_Type_L1HvdFG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_Type_L1HvdFG r v)

def _set_ID_MMFR2_EL1_Type_L1HvdRng (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_L1HvdRng r v)

def _set_ID_MMFR2_Type_L1HvdRng (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_Type_L1HvdRng r v)

def _set_ID_MMFR2_EL1_Type_MemBarr (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_MemBarr r v)

def _set_ID_MMFR2_Type_MemBarr (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_Type_MemBarr r v)

def _set_ID_MMFR2_EL1_Type_UniTLB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_UniTLB r v)

def _set_ID_MMFR2_Type_UniTLB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_Type_UniTLB r v)

def _set_ID_MMFR2_EL1_Type_WFIStall (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_EL1_Type_WFIStall r v)

def _set_ID_MMFR2_Type_WFIStall (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR2_Type_WFIStall r v)

def _set_ID_MMFR4_EL1_Type_AC2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_AC2 r v)

def _set_ID_MMFR4_Type_AC2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_Type_AC2 r v)

def _set_ID_MMFR4_EL1_Type_CCIDX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_CCIDX r v)

def _set_ID_AA64MMFR2_EL1_Type_CCIDX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_CCIDX r v)

def _set_ID_MMFR4_Type_CCIDX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_Type_CCIDX r v)

def _set_ID_MMFR4_EL1_Type_EVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_EVT r v)

def _set_ID_AA64MMFR2_EL1_Type_EVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_EVT r v)

def _set_ID_MMFR4_Type_EVT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_Type_EVT r v)

def _set_ID_MMFR4_EL1_Type_HPDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_HPDS r v)

def _set_ID_AA64MMFR1_EL1_Type_HPDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_HPDS r v)

def _set_ID_MMFR4_Type_HPDS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_Type_HPDS r v)

def _set_ID_MMFR4_EL1_Type_LSM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_LSM r v)

def _set_ID_AA64MMFR2_EL1_Type_LSM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_LSM r v)

def _set_ID_MMFR4_Type_LSM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_Type_LSM r v)

def _set_ID_MMFR4_EL1_Type_SpecSEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_SpecSEI r v)

def _set_ID_AA64MMFR1_EL1_Type_SpecSEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_SpecSEI r v)

def _set_ID_MMFR4_Type_SpecSEI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_Type_SpecSEI r v)

def _set_ID_MMFR4_EL1_Type_XNX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_XNX r v)

def _set_ID_AA64MMFR1_EL1_Type_XNX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_XNX r v)

def _set_ID_MMFR4_Type_XNX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR4_Type_XNX r v)

def _set_ID_AA64MMFR2_EL1_Type_BBM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_BBM r v)

def _set_ID_AA64MMFR2_EL1_Type_E0PD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_E0PD r v)

def _set_ID_AA64MMFR2_EL1_Type_TTL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_TTL r v)

def _set_ID_AA64MMFR2_EL1_Type_VARange (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_VARange r v)

def _set_HDFGRTR_EL2_Type_DBGAUTHSTATUS_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGAUTHSTATUS_EL1 r v)

def _set_HDFGRTR_EL2_Type_DBGBCRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGBCRn_EL1 r v)

def _set_HDFGWTR_EL2_Type_DBGBCRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGBCRn_EL1 r v)

def _set_HDFGRTR_EL2_Type_DBGBVRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGBVRn_EL1 r v)

def _set_HDFGWTR_EL2_Type_DBGBVRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGBVRn_EL1 r v)

def _set_HDFGRTR_EL2_Type_DBGCLAIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGCLAIM r v)

def _set_HDFGWTR_EL2_Type_DBGCLAIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGCLAIM r v)

def _set_HDFGRTR_EL2_Type_DBGPRCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGPRCR_EL1 r v)

def _set_HDFGWTR_EL2_Type_DBGPRCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGPRCR_EL1 r v)

def _set_HDFGRTR_EL2_Type_DBGWCRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGWCRn_EL1 r v)

def _set_HDFGWTR_EL2_Type_DBGWCRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGWCRn_EL1 r v)

def _set_HDFGRTR_EL2_Type_DBGWVRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGWVRn_EL1 r v)

def _set_HDFGWTR_EL2_Type_DBGWVRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGWVRn_EL1 r v)

def _set_HDFGRTR_EL2_Type_MDSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_MDSCR_EL1 r v)

def _set_HDFGWTR_EL2_Type_MDSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_MDSCR_EL1 r v)

def _set_HDFGRTR_EL2_Type_OSDLR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_OSDLR_EL1 r v)

def _set_HDFGWTR_EL2_Type_OSDLR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_OSDLR_EL1 r v)

def _set_HDFGRTR_EL2_Type_OSECCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_OSECCR_EL1 r v)

def _set_HDFGWTR_EL2_Type_OSECCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_OSECCR_EL1 r v)

def _set_HDFGRTR_EL2_Type_OSLSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_OSLSR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMBIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMBIDR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMBLIMITR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMBLIMITR_EL1 r v)

def _set_HDFGWTR_EL2_Type_PMBLIMITR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMBLIMITR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMBPTR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMBPTR_EL1 r v)

def _set_HDFGWTR_EL2_Type_PMBPTR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMBPTR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMBSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMBSR_EL1 r v)

def _set_HDFGWTR_EL2_Type_PMBSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMBSR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMCCFILTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMCCFILTR_EL0 r v)

def _set_HDFGWTR_EL2_Type_PMCCFILTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMCCFILTR_EL0 r v)

def _set_HDFGRTR_EL2_Type_PMCCNTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMCCNTR_EL0 r v)

def _set_HDFGWTR_EL2_Type_PMCCNTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMCCNTR_EL0 r v)

def _set_HDFGRTR_EL2_Type_PMCEIDn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMCEIDn_EL0 r v)

def _set_HDFGRTR_EL2_Type_PMCNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMCNTEN r v)

def _set_HDFGWTR_EL2_Type_PMCNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMCNTEN r v)

def _set_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 r v)

def _set_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 r v)

def _set_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 r v)

def _set_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 r v)

def _set_HDFGRTR_EL2_Type_PMINTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMINTEN r v)

def _set_HDFGWTR_EL2_Type_PMINTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMINTEN r v)

def _set_HDFGRTR_EL2_Type_PMMIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMMIR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMOVS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMOVS r v)

def _set_HDFGWTR_EL2_Type_PMOVS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMOVS r v)

def _set_HDFGRTR_EL2_Type_PMSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSCR_EL1 r v)

def _set_HDFGWTR_EL2_Type_PMSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSCR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMSELR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSELR_EL0 r v)

def _set_HDFGWTR_EL2_Type_PMSELR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSELR_EL0 r v)

def _set_HDFGRTR_EL2_Type_PMSEVFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSEVFR_EL1 r v)

def _set_HDFGWTR_EL2_Type_PMSEVFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSEVFR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMSFCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSFCR_EL1 r v)

def _set_HDFGWTR_EL2_Type_PMSFCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSFCR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMSICR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSICR_EL1 r v)

def _set_HDFGWTR_EL2_Type_PMSICR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSICR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMSIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSIDR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMSIRR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSIRR_EL1 r v)

def _set_HDFGWTR_EL2_Type_PMSIRR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSIRR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMSLATFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSLATFR_EL1 r v)

def _set_HDFGWTR_EL2_Type_PMSLATFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSLATFR_EL1 r v)

def _set_HDFGRTR_EL2_Type_PMUSERENR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMUSERENR_EL0 r v)

def _set_HDFGWTR_EL2_Type_PMUSERENR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMUSERENR_EL0 r v)

def _set_HDFGRTR_EL2_Type_TRC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRC r v)

def _set_HDFGWTR_EL2_Type_TRC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRC r v)

def _set_HDFGRTR_EL2_Type_TRCAUTHSTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCAUTHSTATUS r v)

def _set_HDFGRTR_EL2_Type_TRCAUXCTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCAUXCTLR r v)

def _set_HDFGWTR_EL2_Type_TRCAUXCTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCAUXCTLR r v)

def _set_HDFGRTR_EL2_Type_TRCCLAIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCCLAIM r v)

def _set_HDFGWTR_EL2_Type_TRCCLAIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCCLAIM r v)

def _set_HDFGRTR_EL2_Type_TRCCNTVRn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCCNTVRn r v)

def _set_HDFGWTR_EL2_Type_TRCCNTVRn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCCNTVRn r v)

def _set_HDFGRTR_EL2_Type_TRCID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCID r v)

def _set_HDFGRTR_EL2_Type_TRCIMSPECn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCIMSPECn r v)

def _set_HDFGWTR_EL2_Type_TRCIMSPECn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCIMSPECn r v)

def _set_HDFGRTR_EL2_Type_TRCOSLSR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCOSLSR r v)

def _set_HDFGRTR_EL2_Type_TRCPRGCTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCPRGCTLR r v)

def _set_HDFGWTR_EL2_Type_TRCPRGCTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCPRGCTLR r v)

def _set_HDFGRTR_EL2_Type_TRCSEQSTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCSEQSTR r v)

def _set_HDFGWTR_EL2_Type_TRCSEQSTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCSEQSTR r v)

def _set_HDFGRTR_EL2_Type_TRCSSCSRn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCSSCSRn r v)

def _set_HDFGWTR_EL2_Type_TRCSSCSRn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCSSCSRn r v)

def _set_HDFGRTR_EL2_Type_TRCSTATR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCSTATR r v)

def _set_HDFGRTR_EL2_Type_TRCVICTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCVICTLR r v)

def _set_HDFGWTR_EL2_Type_TRCVICTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCVICTLR r v)

def _set_HDFGRTR_EL2_Type_nBRBCTL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_nBRBCTL r v)

def _set_HDFGWTR_EL2_Type_nBRBCTL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_nBRBCTL r v)

def _set_HDFGRTR_EL2_Type_nBRBDATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_nBRBDATA r v)

def _set_HDFGWTR_EL2_Type_nBRBDATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_nBRBDATA r v)

def _set_HDFGRTR_EL2_Type_nBRBIDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_nBRBIDR r v)

def _set_HDFGRTR_EL2_Type_nPMSNEVFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_nPMSNEVFR_EL1 r v)

def _set_HDFGWTR_EL2_Type_nPMSNEVFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_nPMSNEVFR_EL1 r v)

def _set_ICV_NMIAR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_NMIAR1_EL1_Type_INTID r v)

def _set_GICC_AEOIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_AEOIR_Type_INTID r v)

def _set_GICC_AHPPIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_AHPPIR_Type_INTID r v)

def _set_GICC_AIAR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_AIAR_Type_INTID r v)

def _set_GICC_DIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_DIR_Type_INTID r v)

def _set_GICC_EOIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_EOIR_Type_INTID r v)

def _set_GICC_HPPIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_HPPIR_Type_INTID r v)

def _set_GICC_IAR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_IAR_Type_INTID r v)

def _set_GICD_CLRSPI_NSR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CLRSPI_NSR_Type_INTID r v)

def _set_GICD_CLRSPI_SR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CLRSPI_SR_Type_INTID r v)

def _set_GICD_SETSPI_NSR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_SETSPI_NSR_Type_INTID r v)

def _set_GICD_SETSPI_SR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_SETSPI_SR_Type_INTID r v)

def _set_GICD_SGIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_SGIR_Type_INTID r v)

def _set_GICM_CLRSPI_NSR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_CLRSPI_NSR_Type_INTID r v)

def _set_GICM_CLRSPI_SR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_CLRSPI_SR_Type_INTID r v)

def _set_GICM_SETSPI_NSR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_SETSPI_NSR_Type_INTID r v)

def _set_GICM_SETSPI_SR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_SETSPI_SR_Type_INTID r v)

def _set_GICM_TYPER_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_TYPER_Type_INTID r v)

def _set_GICR_INVLPIR_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INVLPIR_Type_INTID r v)

def _set_GICV_AEOIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_AEOIR_Type_INTID r v)

def _set_GICV_AHPPIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_AHPPIR_Type_INTID r v)

def _set_GICV_AIAR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_AIAR_Type_INTID r v)

def _set_GICV_DIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_DIR_Type_INTID r v)

def _set_GICV_EOIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_EOIR_Type_INTID r v)

def _set_GICV_HPPIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_HPPIR_Type_INTID r v)

def _set_GICV_IAR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_IAR_Type_INTID r v)

def _set_ICC_ASGI1R_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_INTID r v)

def _set_ICC_ASGI1R_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_INTID r v)

def _set_ICC_DIR_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_DIR_EL1_Type_INTID r v)

def _set_ICC_DIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_DIR_Type_INTID r v)

def _set_ICC_EOIR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_EOIR0_EL1_Type_INTID r v)

def _set_ICC_EOIR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_EOIR0_Type_INTID r v)

def _set_ICC_EOIR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_EOIR1_EL1_Type_INTID r v)

def _set_ICC_EOIR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_EOIR1_Type_INTID r v)

def _set_ICC_HPPIR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HPPIR0_EL1_Type_INTID r v)

def _set_ICC_HPPIR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HPPIR0_Type_INTID r v)

def _set_ICC_HPPIR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HPPIR1_EL1_Type_INTID r v)

def _set_ICC_HPPIR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HPPIR1_Type_INTID r v)

def _set_ICC_IAR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IAR0_EL1_Type_INTID r v)

def _set_ICC_IAR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IAR0_Type_INTID r v)

def _set_ICC_IAR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IAR1_EL1_Type_INTID r v)

def _set_ICC_IAR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IAR1_Type_INTID r v)

def _set_ICC_NMIAR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_NMIAR1_EL1_Type_INTID r v)

def _set_ICC_SGI0R_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_INTID r v)

def _set_ICC_SGI0R_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_Type_INTID r v)

def _set_ICC_SGI1R_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_INTID r v)

def _set_ICC_SGI1R_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_Type_INTID r v)

def _set_ICV_DIR_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_DIR_EL1_Type_INTID r v)

def _set_ICV_DIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_DIR_Type_INTID r v)

def _set_ICV_EOIR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_EOIR0_EL1_Type_INTID r v)

def _set_ICV_EOIR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_EOIR0_Type_INTID r v)

def _set_ICV_EOIR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_EOIR1_EL1_Type_INTID r v)

def _set_ICV_EOIR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_EOIR1_Type_INTID r v)

def _set_ICV_HPPIR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_HPPIR0_EL1_Type_INTID r v)

def _set_ICV_HPPIR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_HPPIR0_Type_INTID r v)

def _set_ICV_HPPIR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_HPPIR1_EL1_Type_INTID r v)

def _set_ICV_HPPIR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_HPPIR1_Type_INTID r v)

def _set_ICV_IAR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IAR0_EL1_Type_INTID r v)

def _set_ICV_IAR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IAR0_Type_INTID r v)

def _set_ICV_IAR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IAR1_EL1_Type_INTID r v)

def _set_ICV_IAR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IAR1_Type_INTID r v)

def _set_ICH_LR_EL2_Type_Group (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_Group r v)

def _set_ICH_LRC_Type_Group (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LRC_Type_Group r v)

def _set_ICH_LR_EL2_Type_HW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_HW r v)

def _set_ICH_LRC_Type_HW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LRC_Type_HW r v)

def _set_ICH_LR_EL2_Type_State (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_State r v)

def _set_ICH_LRC_Type_State (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LRC_Type_State r v)

def _set_ICH_LR_EL2_Type_pINTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_pINTID r v)

def _set_GICR_CLRLPIR_Type_pINTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CLRLPIR_Type_pINTID r v)

def _set_GICR_SETLPIR_Type_pINTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_SETLPIR_Type_pINTID r v)

def _set_ICH_LRC_Type_pINTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LRC_Type_pINTID r v)

def _set_ICH_LR_EL2_Type_vINTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_vINTID r v)

def _set_GITS_SGIR_Type_vINTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_SGIR_Type_vINTID r v)

def _set_ICH_LR_Type_vINTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_LR_Type_vINTID r v)

def _set_MVFR0_EL1_Type_FPDP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPDP r v)

def _set_MVFR0_Type_FPDP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_Type_FPDP r v)

def _set_MVFR0_EL1_Type_FPDivide (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPDivide r v)

def _set_MVFR0_Type_FPDivide (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_Type_FPDivide r v)

def _set_MVFR0_EL1_Type_FPRound (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPRound r v)

def _set_MVFR0_Type_FPRound (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_Type_FPRound r v)

def _set_MVFR0_EL1_Type_FPSP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPSP r v)

def _set_MVFR0_Type_FPSP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_Type_FPSP r v)

def _set_MVFR0_EL1_Type_FPShVec (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPShVec r v)

def _set_MVFR0_Type_FPShVec (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_Type_FPShVec r v)

def _set_MVFR0_EL1_Type_FPSqrt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPSqrt r v)

def _set_MVFR0_Type_FPSqrt (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_Type_FPSqrt r v)

def _set_MVFR0_EL1_Type_FPTrap (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPTrap r v)

def _set_MVFR0_Type_FPTrap (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_Type_FPTrap r v)

def _set_MVFR0_EL1_Type_SIMDReg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_EL1_Type_SIMDReg r v)

def _set_MVFR0_Type_SIMDReg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR0_Type_SIMDReg r v)

def _set_ID_AA64DFR0_EL1_Type_BRBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_BRBE r v)

def _set_ID_AA64DFR0_EL1_Type_BRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_BRPs r v)

def _set_DBGDIDR_Type_BRPs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDIDR_Type_BRPs r v)

def _set_EDDFR1_Type_BRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_BRPs r v)

def _set_EDDFR_Type_BRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR_Type_BRPs r v)

def _set_ID_AA64DFR1_EL1_Type_BRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_BRPs r v)

def _set_ID_AA64DFR0_EL1_Type_CTX_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_CTX_CMPs r v)

def _set_DBGDIDR_Type_CTX_CMPs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDIDR_Type_CTX_CMPs r v)

def _set_EDDFR1_Type_CTX_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_CTX_CMPs r v)

def _set_EDDFR_Type_CTX_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR_Type_CTX_CMPs r v)

def _set_ID_AA64DFR1_EL1_Type_CTX_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_CTX_CMPs r v)

def _set_ID_AA64DFR0_EL1_Type_DebugVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_DebugVer r v)

def _set_ID_AA64DFR0_EL1_Type_DoubleLock (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_DoubleLock r v)

def _set_DBGDEVID_Type_DoubleLock (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID_Type_DoubleLock r v)

def _set_ID_AA64DFR0_EL1_Type_ExtTrcBuff (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_ExtTrcBuff r v)

def _set_EDDFR_Type_ExtTrcBuff (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR_Type_ExtTrcBuff r v)

def _set_ID_AA64DFR0_EL1_Type_HPMN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_HPMN0 r v)

def _set_ID_DFR1_EL1_Type_HPMN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR1_EL1_Type_HPMN0 r v)

def _set_ID_DFR1_Type_HPMN0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR1_Type_HPMN0 r v)

def _set_ID_AA64DFR0_EL1_Type_MTPMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_MTPMU r v)

def _set_ID_DFR1_EL1_Type_MTPMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR1_EL1_Type_MTPMU r v)

def _set_ID_DFR1_Type_MTPMU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR1_Type_MTPMU r v)

def _set_ID_AA64DFR0_EL1_Type_PMSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_PMSS r v)

def _set_EDDFR_Type_PMSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR_Type_PMSS r v)

def _set_PMDEVID_Type_PMSS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMDEVID_Type_PMSS r v)

def _set_ID_AA64DFR0_EL1_Type_PMSVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_PMSVer r v)

def _set_ID_AA64DFR0_EL1_Type_PMUVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_PMUVer r v)

def _set_EDDFR_Type_PMUVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR_Type_PMUVer r v)

def _set_ID_AA64DFR0_EL1_Type_SEBEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_SEBEP r v)

def _set_EDDFR_Type_SEBEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR_Type_SEBEP r v)

def _set_ID_AA64DFR0_EL1_Type_TraceBuffer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_TraceBuffer r v)

def _set_ID_AA64DFR0_EL1_Type_TraceFilt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_TraceFilt r v)

def _set_EDDFR_Type_TraceFilt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR_Type_TraceFilt r v)

def _set_ID_DFR0_EL1_Type_TraceFilt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_TraceFilt r v)

def _set_ID_DFR0_Type_TraceFilt (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_Type_TraceFilt r v)

def _set_ID_AA64DFR0_EL1_Type_TraceVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_TraceVer r v)

def _set_EDDFR_Type_TraceVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR_Type_TraceVer r v)

def _set_ID_AA64DFR0_EL1_Type_WRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_WRPs r v)

def _set_DBGDIDR_Type_WRPs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDIDR_Type_WRPs r v)

def _set_EDDFR1_Type_WRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_WRPs r v)

def _set_EDDFR_Type_WRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR_Type_WRPs r v)

def _set_ID_AA64DFR1_EL1_Type_WRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_WRPs r v)

def _set_ICV_BPR1_EL1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_BPR1_EL1_Type_BinaryPoint r v)

def _set_ICC_BPR0_EL1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_BPR0_EL1_Type_BinaryPoint r v)

def _set_ICC_BPR0_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_BPR0_Type_BinaryPoint r v)

def _set_ICC_BPR1_EL1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_BPR1_EL1_Type_BinaryPoint r v)

def _set_ICC_BPR1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_BPR1_Type_BinaryPoint r v)

def _set_ICV_BPR0_EL1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_BPR0_EL1_Type_BinaryPoint r v)

def _set_ICV_BPR0_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_BPR0_Type_BinaryPoint r v)

def _set_ICV_BPR1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_BPR1_Type_BinaryPoint r v)

def _set_ID_ISAR2_EL1_Type_LoadStore (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_LoadStore r v)

def _set_ID_ISAR2_Type_LoadStore (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_Type_LoadStore r v)

def _set_ID_ISAR2_EL1_Type_MemHint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_MemHint r v)

def _set_ID_ISAR2_Type_MemHint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_Type_MemHint r v)

def _set_ID_ISAR2_EL1_Type_Mult (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_Mult r v)

def _set_ID_ISAR2_Type_Mult (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_Type_Mult r v)

def _set_ID_ISAR2_EL1_Type_MultS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_MultS r v)

def _set_ID_ISAR2_Type_MultS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_Type_MultS r v)

def _set_ID_ISAR2_EL1_Type_MultU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_MultU r v)

def _set_ID_ISAR2_Type_MultU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_Type_MultU r v)

def _set_ID_ISAR2_EL1_Type_MultiAccessInt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_MultiAccessInt r v)

def _set_ID_ISAR2_Type_MultiAccessInt (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_Type_MultiAccessInt r v)

def _set_ID_ISAR2_EL1_Type_PSR_AR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_PSR_AR r v)

def _set_ID_ISAR2_Type_PSR_AR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_Type_PSR_AR r v)

def _set_ID_ISAR2_EL1_Type_Reversal (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_Reversal r v)

def _set_ID_ISAR2_Type_Reversal (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR2_Type_Reversal r v)

def _set_PMECR_EL1_Type_KPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMECR_EL1_Type_KPME r v)

def _set_PMECR_EL1_Type_SSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMECR_EL1_Type_SSE r v)

def _set_RMR_EL1_Type_AA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_EL1_Type_AA64 r v)

def _set_HRMR_Type_AA64 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HRMR_Type_AA64 r v)

def _set_RMR_EL2_Type_AA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_EL2_Type_AA64 r v)

def _set_RMR_EL3_Type_AA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_EL3_Type_AA64 r v)

def _set_RMR_Type_AA64 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_Type_AA64 r v)

def _set_RMR_EL1_Type_RR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_EL1_Type_RR r v)

def _set_HRMR_Type_RR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HRMR_Type_RR r v)

def _set_RMR_EL2_Type_RR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_EL2_Type_RR r v)

def _set_RMR_EL3_Type_RR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_EL3_Type_RR r v)

def _set_RMR_Type_RR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RMR_Type_RR r v)

def _set_HAFGRTR_EL2_Type_AMCNTEN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMCNTEN0 r v)

def _set_HAFGRTR_EL2_Type_AMCNTEN1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMCNTEN1 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR00_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR00_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR01_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR01_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR02_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR02_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR03_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR03_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR10_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR10_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR10_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR10_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR110_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR110_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR110_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR110_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR111_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR111_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR111_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR111_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR112_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR112_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR112_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR112_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR113_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR113_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR113_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR113_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR114_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR114_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR114_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR114_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR115_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR115_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR115_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR115_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR11_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR11_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR11_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR11_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR12_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR12_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR12_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR12_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR13_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR13_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR13_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR13_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR14_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR14_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR14_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR14_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR15_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR15_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR15_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR15_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR16_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR16_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR16_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR16_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR17_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR17_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR17_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR17_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR18_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR18_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR18_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR18_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVCNTR19_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR19_EL0 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTR19_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR19_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER10_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER10_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER110_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER110_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER111_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER111_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER112_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER112_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER113_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER113_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER114_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER114_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER115_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER115_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER11_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER11_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER12_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER12_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER13_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER13_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER14_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER14_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER15_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER15_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER16_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER16_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER17_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER17_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER18_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER18_EL0 r v)

def _set_HAFGRTR_EL2_Type_AMEVTYPER19_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER19_EL0 r v)

def _set_ID_AA64DFR1_EL1_Type_ABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_ABLE r v)

def _set_EDDFR1_Type_ABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_ABLE r v)

def _set_ID_AA64DFR1_EL1_Type_ABL_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_ABL_CMPs r v)

def _set_EDDFR1_Type_ABL_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_ABL_CMPs r v)

def _set_ID_AA64DFR1_EL1_Type_DPFZS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_DPFZS r v)

def _set_ID_AA64DFR1_EL1_Type_EBEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_EBEP r v)

def _set_EDDFR1_Type_EBEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_EBEP r v)

def _set_ID_AA64DFR1_EL1_Type_PMICNTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_PMICNTR r v)

def _set_EDDFR1_Type_PMICNTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_PMICNTR r v)

def _set_ID_AA64DFR1_EL1_Type_SPMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_SPMU r v)

def _set_EDDFR1_Type_SPMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_SPMU r v)

def _set_ID_AA64DFR1_EL1_Type_SYSPMUID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_SYSPMUID r v)

def _set_EDDFR1_Type_SYSPMUID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDFR1_Type_SYSPMUID r v)

def _set_ACCDATA_EL1_Type_ACCDATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ACCDATA_EL1_Type_ACCDATA r v)

def __set_SCTLR_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : SCTLR_EL1_Type := value_name
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL1) 4 0 (BitVec.slice r 0 5))
  writeReg SCTLR_EL1 (BitVec.update (← readReg SCTLR_EL1) 6 (Bit (BitVec.slice r 6 1)))
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL1) 63 8 (BitVec.slice r 8 56))
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_ITD")))) : Bool)
  then writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL1) 7 7 (_get_SCTLR_EL1_Type_ITD r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_CP15BEN")))) : Bool)
  then writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL1) 5 5 (_get_SCTLR_EL1_Type_CP15BEN r))
  else (pure ())

def _set_PMSSCR_EL1_Type_NC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSSCR_EL1_Type_NC r v)

def __set_PMSSCR_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMSSCR_EL1_Type := value_name
  writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSSCR_EL1) 63 1 (BitVec.slice r 1 63))
  if ((! (← (__IMPDEF_boolean "Capture events are disabled"))) : Bool)
  then writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSSCR_EL1) 0 0 (_get_PMSSCR_EL1_Type_SS r))
  else (pure ())

def _set_LORID_EL1_Type_LR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORID_EL1_Type_LR r v)

def _set_CNTP_TVAL_EL0_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_TVAL_EL0_Type_TimerValue r v)

def _set_CNTHPS_TVAL_EL2_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHPS_TVAL_EL2_Type_TimerValue r v)

def _set_CNTHP_TVAL_EL2_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_TVAL_EL2_Type_TimerValue r v)

def _set_CNTHVS_TVAL_EL2_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHVS_TVAL_EL2_Type_TimerValue r v)

def _set_CNTHV_TVAL_EL2_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHV_TVAL_EL2_Type_TimerValue r v)

def _set_CNTPS_TVAL_EL1_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTPS_TVAL_EL1_Type_TimerValue r v)

def _set_CNTV_TVAL_EL0_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTV_TVAL_EL0_Type_TimerValue r v)

def _set_ID_AA64ISAR1_EL1_Type_APA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_APA r v)

def _set_ID_AA64ISAR1_EL1_Type_BF16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_BF16 r v)

def _set_ID_AA64ZFR0_EL1_Type_BF16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_BF16 r v)

def _set_ID_ISAR6_EL1_Type_BF16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_BF16 r v)

def _set_ID_ISAR6_Type_BF16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_Type_BF16 r v)

def _set_ID_AA64ISAR1_EL1_Type_DGH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_DGH r v)

def _set_ID_AA64ISAR1_EL1_Type_DPB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_DPB r v)

def _set_ID_AA64ISAR1_EL1_Type_FCMA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_FCMA r v)

def _set_ID_AA64ISAR1_EL1_Type_FRINTTS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_FRINTTS r v)

def _set_ID_AA64ISAR1_EL1_Type_GPA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_GPA r v)

def _set_ID_AA64ISAR1_EL1_Type_GPI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_GPI r v)

def _set_ID_AA64ISAR1_EL1_Type_I8MM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_I8MM r v)

def _set_ID_AA64ZFR0_EL1_Type_I8MM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_I8MM r v)

def _set_ID_ISAR6_EL1_Type_I8MM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_I8MM r v)

def _set_ID_ISAR6_Type_I8MM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_Type_I8MM r v)

def _set_ID_AA64ISAR1_EL1_Type_JSCVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_JSCVT r v)

def _set_ID_ISAR6_EL1_Type_JSCVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_JSCVT r v)

def _set_ID_ISAR6_Type_JSCVT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_Type_JSCVT r v)

def _set_ID_AA64ISAR1_EL1_Type_LRCPC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_LRCPC r v)

def _set_ID_AA64ISAR1_EL1_Type_LS64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_LS64 r v)

def _set_ID_AA64ISAR1_EL1_Type_SB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_SB r v)

def _set_ID_ISAR6_EL1_Type_SB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_SB r v)

def _set_ID_ISAR6_Type_SB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_Type_SB r v)

def _set_ID_AA64ISAR1_EL1_Type_SPECRES (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_SPECRES r v)

def _set_ID_ISAR6_EL1_Type_SPECRES (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_SPECRES r v)

def _set_ID_ISAR6_Type_SPECRES (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_Type_SPECRES r v)

def _set_ID_AA64ISAR1_EL1_Type_XS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_XS r v)

def _set_ID_AA64MMFR4_EL1_Type_EIESB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR4_EL1_Type_EIESB r v)

def _set_ICH_EISR_EL2_Type_Status0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status0 r v)

def _set_GICH_EISR_Type_Status0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status0 r v)

def _set_GICH_ELRSR_Type_Status0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status0 r v)

def _set_ICH_EISR_Type_Status0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status0 r v)

def _set_ICH_ELRSR_EL2_Type_Status0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status0 r v)

def _set_ICH_ELRSR_Type_Status0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status0 r v)

def _set_ICH_EISR_EL2_Type_Status1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status1 r v)

def _set_GICH_EISR_Type_Status1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status1 r v)

def _set_GICH_ELRSR_Type_Status1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status1 r v)

def _set_ICH_EISR_Type_Status1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status1 r v)

def _set_ICH_ELRSR_EL2_Type_Status1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status1 r v)

def _set_ICH_ELRSR_Type_Status1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status1 r v)

def _set_ICH_EISR_EL2_Type_Status10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status10 r v)

def _set_GICH_EISR_Type_Status10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status10 r v)

def _set_GICH_ELRSR_Type_Status10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status10 r v)

def _set_ICH_EISR_Type_Status10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status10 r v)

def _set_ICH_ELRSR_EL2_Type_Status10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status10 r v)

def _set_ICH_ELRSR_Type_Status10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status10 r v)

def _set_ICH_EISR_EL2_Type_Status11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status11 r v)

def _set_GICH_EISR_Type_Status11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status11 r v)

def _set_GICH_ELRSR_Type_Status11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status11 r v)

def _set_ICH_EISR_Type_Status11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status11 r v)

def _set_ICH_ELRSR_EL2_Type_Status11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status11 r v)

def _set_ICH_ELRSR_Type_Status11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status11 r v)

def _set_ICH_EISR_EL2_Type_Status12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status12 r v)

def _set_GICH_EISR_Type_Status12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status12 r v)

def _set_GICH_ELRSR_Type_Status12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status12 r v)

def _set_ICH_EISR_Type_Status12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status12 r v)

def _set_ICH_ELRSR_EL2_Type_Status12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status12 r v)

def _set_ICH_ELRSR_Type_Status12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status12 r v)

def _set_ICH_EISR_EL2_Type_Status13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status13 r v)

def _set_GICH_EISR_Type_Status13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status13 r v)

def _set_GICH_ELRSR_Type_Status13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status13 r v)

def _set_ICH_EISR_Type_Status13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status13 r v)

def _set_ICH_ELRSR_EL2_Type_Status13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status13 r v)

def _set_ICH_ELRSR_Type_Status13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status13 r v)

def _set_ICH_EISR_EL2_Type_Status14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status14 r v)

def _set_GICH_EISR_Type_Status14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status14 r v)

def _set_GICH_ELRSR_Type_Status14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status14 r v)

def _set_ICH_EISR_Type_Status14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status14 r v)

def _set_ICH_ELRSR_EL2_Type_Status14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status14 r v)

def _set_ICH_ELRSR_Type_Status14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status14 r v)

def _set_ICH_EISR_EL2_Type_Status15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status15 r v)

def _set_GICH_EISR_Type_Status15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status15 r v)

def _set_GICH_ELRSR_Type_Status15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status15 r v)

def _set_ICH_EISR_Type_Status15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status15 r v)

def _set_ICH_ELRSR_EL2_Type_Status15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status15 r v)

def _set_ICH_ELRSR_Type_Status15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status15 r v)

def _set_ICH_EISR_EL2_Type_Status2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status2 r v)

def _set_GICH_EISR_Type_Status2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status2 r v)

def _set_GICH_ELRSR_Type_Status2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status2 r v)

def _set_ICH_EISR_Type_Status2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status2 r v)

def _set_ICH_ELRSR_EL2_Type_Status2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status2 r v)

def _set_ICH_ELRSR_Type_Status2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status2 r v)

def _set_ICH_EISR_EL2_Type_Status3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status3 r v)

def _set_GICH_EISR_Type_Status3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status3 r v)

def _set_GICH_ELRSR_Type_Status3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status3 r v)

def _set_ICH_EISR_Type_Status3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status3 r v)

def _set_ICH_ELRSR_EL2_Type_Status3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status3 r v)

def _set_ICH_ELRSR_Type_Status3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status3 r v)

def _set_ICH_EISR_EL2_Type_Status4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status4 r v)

def _set_GICH_EISR_Type_Status4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status4 r v)

def _set_GICH_ELRSR_Type_Status4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status4 r v)

def _set_ICH_EISR_Type_Status4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status4 r v)

def _set_ICH_ELRSR_EL2_Type_Status4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status4 r v)

def _set_ICH_ELRSR_Type_Status4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status4 r v)

def _set_ICH_EISR_EL2_Type_Status5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status5 r v)

def _set_GICH_EISR_Type_Status5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status5 r v)

def _set_GICH_ELRSR_Type_Status5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status5 r v)

def _set_ICH_EISR_Type_Status5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status5 r v)

def _set_ICH_ELRSR_EL2_Type_Status5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status5 r v)

def _set_ICH_ELRSR_Type_Status5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status5 r v)

def _set_ICH_EISR_EL2_Type_Status6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status6 r v)

def _set_GICH_EISR_Type_Status6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status6 r v)

def _set_GICH_ELRSR_Type_Status6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status6 r v)

def _set_ICH_EISR_Type_Status6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status6 r v)

def _set_ICH_ELRSR_EL2_Type_Status6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status6 r v)

def _set_ICH_ELRSR_Type_Status6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status6 r v)

def _set_ICH_EISR_EL2_Type_Status7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status7 r v)

def _set_GICH_EISR_Type_Status7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status7 r v)

def _set_GICH_ELRSR_Type_Status7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status7 r v)

def _set_ICH_EISR_Type_Status7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status7 r v)

def _set_ICH_ELRSR_EL2_Type_Status7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status7 r v)

def _set_ICH_ELRSR_Type_Status7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status7 r v)

def _set_ICH_EISR_EL2_Type_Status8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status8 r v)

def _set_GICH_EISR_Type_Status8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status8 r v)

def _set_GICH_ELRSR_Type_Status8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status8 r v)

def _set_ICH_EISR_Type_Status8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status8 r v)

def _set_ICH_ELRSR_EL2_Type_Status8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status8 r v)

def _set_ICH_ELRSR_Type_Status8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status8 r v)

def _set_ICH_EISR_EL2_Type_Status9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status9 r v)

def _set_GICH_EISR_Type_Status9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_EISR_Type_Status9 r v)

def _set_GICH_ELRSR_Type_Status9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status9 r v)

def _set_ICH_EISR_Type_Status9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_EISR_Type_Status9 r v)

def _set_ICH_ELRSR_EL2_Type_Status9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status9 r v)

def _set_ICH_ELRSR_Type_Status9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status9 r v)

def _set_MIDR_EL1_Type_Architecture (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_EL1_Type_Architecture r v)

def _set_MIDR_Type_Architecture (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_Type_Architecture r v)

def _set_VPIDR_EL2_Type_Architecture (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_EL2_Type_Architecture r v)

def _set_VPIDR_Type_Architecture (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_Type_Architecture r v)

def _set_MIDR_EL1_Type_Implementer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_EL1_Type_Implementer r v)

def _set_AMIIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMIIDR_Type_Implementer r v)

def _set_FPSID_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSID_Type_Implementer r v)

def _set_GICD_IIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_IIDR_Type_Implementer r v)

def _set_GICM_IIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_IIDR_Type_Implementer r v)

def _set_GICR_IIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_IIDR_Type_Implementer r v)

def _set_GITS_IIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_IIDR_Type_Implementer r v)

def _set_MIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_Type_Implementer r v)

def _set_SMIDR_EL1_Type_Implementer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMIDR_EL1_Type_Implementer r v)

def _set_VPIDR_EL2_Type_Implementer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_EL2_Type_Implementer r v)

def _set_VPIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_Type_Implementer r v)

def _set_MIDR_EL1_Type_PartNum (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_EL1_Type_PartNum r v)

def _set_FPSID_Type_PartNum (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSID_Type_PartNum r v)

def _set_MIDR_Type_PartNum (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_Type_PartNum r v)

def _set_VPIDR_EL2_Type_PartNum (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_EL2_Type_PartNum r v)

def _set_VPIDR_Type_PartNum (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_Type_PartNum r v)

def _set_MIDR_EL1_Type_Revision (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_EL1_Type_Revision r v)

def _set_AMIIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMIIDR_Type_Revision r v)

def _set_FPSID_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSID_Type_Revision r v)

def _set_GICD_IIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_IIDR_Type_Revision r v)

def _set_GICM_IIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_IIDR_Type_Revision r v)

def _set_GICR_IIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_IIDR_Type_Revision r v)

def _set_GITS_IIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_IIDR_Type_Revision r v)

def _set_MIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_Type_Revision r v)

def _set_PMIIDR_Type_Revision (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMIIDR_Type_Revision r v)

def _set_SMIDR_EL1_Type_Revision (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMIDR_EL1_Type_Revision r v)

def _set_VPIDR_EL2_Type_Revision (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_EL2_Type_Revision r v)

def _set_VPIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_Type_Revision r v)

def _set_MIDR_EL1_Type_Variant (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_EL1_Type_Variant r v)

def _set_AMIIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMIIDR_Type_Variant r v)

def _set_FPSID_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSID_Type_Variant r v)

def _set_GICD_IIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_IIDR_Type_Variant r v)

def _set_GICM_IIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_IIDR_Type_Variant r v)

def _set_GICR_IIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_IIDR_Type_Variant r v)

def _set_GITS_IIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_IIDR_Type_Variant r v)

def _set_MIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MIDR_Type_Variant r v)

def _set_PMIIDR_Type_Variant (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMIIDR_Type_Variant r v)

def _set_VPIDR_EL2_Type_Variant (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_EL2_Type_Variant r v)

def _set_VPIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VPIDR_Type_Variant r v)

def _set_ICC_RPR_EL1_Type_NMI_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_RPR_EL1_Type_NMI_NS r v)

def _set_ICC_SGI0R_EL1_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_Aff1 r v)

def _set_GITS_MPIDR_Type_Aff1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_MPIDR_Type_Aff1 r v)

def _set_ICC_ASGI1R_EL1_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_Aff1 r v)

def _set_ICC_ASGI1R_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_Aff1 r v)

def _set_ICC_SGI0R_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_Type_Aff1 r v)

def _set_ICC_SGI1R_EL1_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_Aff1 r v)

def _set_ICC_SGI1R_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_Type_Aff1 r v)

def _set_MPIDR_EL1_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_EL1_Type_Aff1 r v)

def _set_MPIDR_Type_Aff1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_Type_Aff1 r v)

def _set_VMPIDR_EL2_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_Aff1 r v)

def _set_VMPIDR_Type_Aff1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_Type_Aff1 r v)

def _set_ICC_SGI0R_EL1_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_Aff2 r v)

def _set_GITS_MPIDR_Type_Aff2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_MPIDR_Type_Aff2 r v)

def _set_ICC_ASGI1R_EL1_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_Aff2 r v)

def _set_ICC_ASGI1R_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_Aff2 r v)

def _set_ICC_SGI0R_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_Type_Aff2 r v)

def _set_ICC_SGI1R_EL1_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_Aff2 r v)

def _set_ICC_SGI1R_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_Type_Aff2 r v)

def _set_MPIDR_EL1_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_EL1_Type_Aff2 r v)

def _set_MPIDR_Type_Aff2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_Type_Aff2 r v)

def _set_VMPIDR_EL2_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_Aff2 r v)

def _set_VMPIDR_Type_Aff2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_Type_Aff2 r v)

def _set_ICC_SGI0R_EL1_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_Aff3 r v)

def _set_GITS_MPIDR_Type_Aff3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_MPIDR_Type_Aff3 r v)

def _set_ICC_ASGI1R_EL1_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_Aff3 r v)

def _set_ICC_ASGI1R_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_Aff3 r v)

def _set_ICC_SGI0R_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_Type_Aff3 r v)

def _set_ICC_SGI1R_EL1_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_Aff3 r v)

def _set_ICC_SGI1R_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_Type_Aff3 r v)

def _set_MPIDR_EL1_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_EL1_Type_Aff3 r v)

def _set_VMPIDR_EL2_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_Aff3 r v)

def _set_ICC_SGI0R_EL1_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_IRM r v)

def _set_ICC_ASGI1R_EL1_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_IRM r v)

def _set_ICC_ASGI1R_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_IRM r v)

def _set_ICC_SGI0R_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_Type_IRM r v)

def _set_ICC_SGI1R_EL1_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_IRM r v)

def _set_ICC_SGI1R_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_Type_IRM r v)

def _set_ICC_SGI0R_EL1_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_RS r v)

def _set_ICC_ASGI1R_EL1_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_RS r v)

def _set_ICC_ASGI1R_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_RS r v)

def _set_ICC_SGI0R_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_Type_RS r v)

def _set_ICC_SGI1R_EL1_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_RS r v)

def _set_ICC_SGI1R_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_Type_RS r v)

def _set_ICC_SGI0R_EL1_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_TargetList r v)

def _set_ICC_ASGI1R_EL1_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_TargetList r v)

def _set_ICC_ASGI1R_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_TargetList r v)

def _set_ICC_SGI0R_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI0R_Type_TargetList r v)

def _set_ICC_SGI1R_EL1_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_TargetList r v)

def _set_ICC_SGI1R_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SGI1R_Type_TargetList r v)

def __set_FPCR (value_name : (BitVec 64)) : SailM Unit := do
  let r : FPCR_Type := value_name
  writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 7 0 (BitVec.slice r 0 8))
  writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 14 13 (BitVec.slice r 13 2))
  writeReg FPCR (BitVec.update (← readReg FPCR) 19 (Bit (BitVec.slice r 19 1)))
  writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 63 22 (BitVec.slice r 22 42))
  if ((! (← (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ"))) : Bool)
  then writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 21 20 (_get_FPCR_Type_Stride r))
  else (pure ())
  if ((! (← (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ"))) : Bool)
  then writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 18 16 (_get_FPCR_Type_length r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions")))) : Bool)
  then writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 15 15 (_get_FPCR_Type_IDE r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions")))) : Bool)
  then writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 12 12 (_get_FPCR_Type_IXE r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions")))) : Bool)
  then writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 11 11 (_get_FPCR_Type_UFE r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions")))) : Bool)
  then writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 10 10 (_get_FPCR_Type_OFE r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions")))) : Bool)
  then writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 9 9 (_get_FPCR_Type_DZE r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions")))) : Bool)
  then writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 8 8 (_get_FPCR_Type_IOE r))
  else (pure ())

def _set_SPMACCESSR_EL1_Type_P31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P31 r v)

def _set_ICH_AP0R_EL2_Type_P31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P31 r v)

def _set_ICH_AP0R_Type_P31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP0R_Type_P31 r v)

def _set_ICH_AP1R_EL2_Type_P31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P31 r v)

def _set_ICH_AP1R_Type_P31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_AP1R_Type_P31 r v)

def _set_SPMACCESSR_EL2_Type_P31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P31 r v)

def _set_SPMACCESSR_EL3_Type_P31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P31 r v)

def _set_SPMSELR_EL0_Type_SYSPMUSEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SPMSELR_EL0_Type_SYSPMUSEL r v)

def __get_selected_SPMACCESSR_EL1_field (_ : Unit) : SailM (BitVec 2) := do
  let idx ← do (pure ((BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) *i 2))
  (pure (BitVec.slice (← readReg SPMACCESSR_EL1) idx 2))

def _set_ID_AA64PFR1_EL1_Type_CSV2_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_CSV2_frac r v)

def _set_ID_AA64PFR1_EL1_Type_DF2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_DF2 r v)

def _set_ID_AA64PFR1_EL1_Type_GCS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_GCS r v)

def _set_EDHSR_Type_GCS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDHSR_Type_GCS r v)

def _set_ID_AA64PFR1_EL1_Type_MPAM_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_MPAM_frac r v)

def _set_ID_AA64PFR1_EL1_Type_MTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_MTE r v)

def _set_ID_AA64PFR1_EL1_Type_MTEX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_MTEX r v)

def _set_ID_AA64PFR1_EL1_Type_MTE_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_MTE_frac r v)

def _set_ID_AA64PFR1_EL1_Type_PFAR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_PFAR r v)

def _set_ID_AA64PFR1_EL1_Type_RAS_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_RAS_frac r v)

def _set_ID_PFR2_EL1_Type_RAS_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR2_EL1_Type_RAS_frac r v)

def _set_ID_PFR2_Type_RAS_frac (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR2_Type_RAS_frac r v)

def _set_ID_AA64PFR1_EL1_Type_RNDR_trap (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_RNDR_trap r v)

def _set_ID_AA64PFR1_EL1_Type_SME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_SME r v)

def _set_ID_AA64PFR1_EL1_Type_THE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_THE r v)

def _set_ID_AA64PFR0_EL1_Type_AMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_AMU r v)

def _set_EDPFR_Type_AMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_AMU r v)

def _set_ID_PFR0_EL1_Type_AMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_AMU r v)

def _set_ID_PFR0_Type_AMU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_Type_AMU r v)

def _set_ID_AA64PFR0_EL1_Type_AdvSIMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_AdvSIMD r v)

def _set_EDPFR_Type_AdvSIMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_AdvSIMD r v)

def _set_ID_AA64PFR0_EL1_Type_CSV2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_CSV2 r v)

def _set_ID_PFR0_EL1_Type_CSV2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_CSV2 r v)

def _set_ID_PFR0_Type_CSV2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_Type_CSV2 r v)

def _set_ID_AA64PFR0_EL1_Type_CSV3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_CSV3 r v)

def _set_ID_PFR2_EL1_Type_CSV3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR2_EL1_Type_CSV3 r v)

def _set_ID_PFR2_Type_CSV3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR2_Type_CSV3 r v)

def _set_ID_AA64PFR0_EL1_Type_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_EL0 r v)

def _set_EDPFR_Type_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_EL0 r v)

def _set_ID_AA64PFR0_EL1_Type_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_EL1 r v)

def _set_EDPFR_Type_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_EL1 r v)

def _set_ID_AA64PFR0_EL1_Type_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_EL2 r v)

def _set_EDAA32PFR_Type_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDAA32PFR_Type_EL2 r v)

def _set_EDPFR_Type_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_EL2 r v)

def _set_ID_AA64PFR0_EL1_Type_EL3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_EL3 r v)

def _set_EDAA32PFR_Type_EL3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDAA32PFR_Type_EL3 r v)

def _set_EDPFR_Type_EL3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_EL3 r v)

def _set_ID_AA64PFR0_EL1_Type_FP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_FP r v)

def _set_EDPFR_Type_FP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_FP r v)

def _set_ID_AA64PFR0_EL1_Type_GIC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_GIC r v)

def _set_EDPFR_Type_GIC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_GIC r v)

def _set_ID_PFR1_EL1_Type_GIC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_GIC r v)

def _set_ID_PFR1_Type_GIC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_Type_GIC r v)

def _set_ID_AA64PFR0_EL1_Type_MPAM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_MPAM r v)

def _set_GITS_TYPER_Type_MPAM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_MPAM r v)

def _set_ID_AA64PFR0_EL1_Type_RAS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_RAS r v)

def _set_ID_PFR0_EL1_Type_RAS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_RAS r v)

def _set_ID_PFR0_Type_RAS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_Type_RAS r v)

def _set_ID_AA64PFR0_EL1_Type_RME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_RME r v)

def _set_ID_AA64PFR0_EL1_Type_SEL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_SEL2 r v)

def _set_EDPFR_Type_SEL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_SEL2 r v)

def _set_ID_AA64PFR0_EL1_Type_SVE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_SVE r v)

def _set_EDPFR_Type_SVE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPFR_Type_SVE r v)

def _set_PMEVCNTSVR_EL1_Type_EVCNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMEVCNTSVR_EL1_Type_EVCNT r v)

def _set_ID_AA64ISAR0_EL1_Type_AES (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_AES r v)

def _set_ID_AA64ZFR0_EL1_Type_AES (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_AES r v)

def _set_ID_ISAR5_EL1_Type_AES (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_EL1_Type_AES r v)

def _set_ID_ISAR5_Type_AES (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_Type_AES r v)

def _set_ID_AA64ISAR0_EL1_Type_Atomic (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_Atomic r v)

def _set_ID_AA64ISAR0_EL1_Type_CRC32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_CRC32 r v)

def _set_ID_ISAR5_EL1_Type_CRC32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_EL1_Type_CRC32 r v)

def _set_ID_ISAR5_Type_CRC32 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_Type_CRC32 r v)

def _set_ID_AA64ISAR0_EL1_Type_FHM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_FHM r v)

def _set_ID_ISAR6_EL1_Type_FHM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_FHM r v)

def _set_ID_ISAR6_Type_FHM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_Type_FHM r v)

def _set_ID_AA64ISAR0_EL1_Type_RDM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_RDM r v)

def _set_ID_ISAR5_EL1_Type_RDM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_EL1_Type_RDM r v)

def _set_ID_ISAR5_Type_RDM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_Type_RDM r v)

def _set_ID_AA64ISAR0_EL1_Type_RNDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_RNDR r v)

def _set_RNDR_Type_RNDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RNDR_Type_RNDR r v)

def _set_ID_AA64ISAR0_EL1_Type_SHA1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_SHA1 r v)

def _set_ID_ISAR5_EL1_Type_SHA1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_EL1_Type_SHA1 r v)

def _set_ID_ISAR5_Type_SHA1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_Type_SHA1 r v)

def _set_ID_AA64ISAR0_EL1_Type_SHA2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_SHA2 r v)

def _set_ID_ISAR5_EL1_Type_SHA2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_EL1_Type_SHA2 r v)

def _set_ID_ISAR5_Type_SHA2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_Type_SHA2 r v)

def _set_ID_AA64ISAR0_EL1_Type_SHA3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_SHA3 r v)

def _set_ID_AA64ZFR0_EL1_Type_SHA3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_SHA3 r v)

def _set_ID_AA64ISAR0_EL1_Type_SM3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_SM3 r v)

def _set_ID_AA64ISAR0_EL1_Type_SM4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_SM4 r v)

def _set_ID_AA64ZFR0_EL1_Type_SM4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_SM4 r v)

def _set_ID_AA64ISAR0_EL1_Type_TLB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR0_EL1_Type_TLB r v)

def _set_PMMIR_EL1_Type_BUS_SLOTS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_EL1_Type_BUS_SLOTS r v)

def _set_PMMIR_Type_BUS_SLOTS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_Type_BUS_SLOTS r v)

def _set_PMMIR_EL1_Type_BUS_WIDTH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_EL1_Type_BUS_WIDTH r v)

def _set_PMMIR_Type_BUS_WIDTH (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_Type_BUS_WIDTH r v)

def _set_PMMIR_EL1_Type_EDGE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_EL1_Type_EDGE r v)

def _set_PMMIR_Type_EDGE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_Type_EDGE r v)

def _set_PMMIR_EL1_Type_SLOTS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_EL1_Type_SLOTS r v)

def _set_PMMIR_Type_SLOTS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_Type_SLOTS r v)

def _set_PMMIR_EL1_Type_THWIDTH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_EL1_Type_THWIDTH r v)

def _set_PMMIR_Type_THWIDTH (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMMIR_Type_THWIDTH r v)

def _set_ICC_IGRPEN1_EL1_Type_Enable (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN1_EL1_Type_Enable r v)

def _set_ICC_HSRE_Type_Enable (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HSRE_Type_Enable r v)

def _set_ICC_IGRPEN0_EL1_Type_Enable (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN0_EL1_Type_Enable r v)

def _set_ICC_IGRPEN0_Type_Enable (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN0_Type_Enable r v)

def _set_ICC_IGRPEN1_Type_Enable (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN1_Type_Enable r v)

def _set_ICC_MSRE_Type_Enable (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MSRE_Type_Enable r v)

def _set_ICC_SRE_EL2_Type_Enable (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL2_Type_Enable r v)

def _set_ICC_SRE_EL3_Type_Enable (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL3_Type_Enable r v)

def _set_ICV_IGRPEN0_EL1_Type_Enable (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IGRPEN0_EL1_Type_Enable r v)

def _set_ICV_IGRPEN0_Type_Enable (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IGRPEN0_Type_Enable r v)

def _set_ICV_IGRPEN1_EL1_Type_Enable (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IGRPEN1_EL1_Type_Enable r v)

def _set_ICV_IGRPEN1_Type_Enable (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_IGRPEN1_Type_Enable r v)

def _set_ID_MMFR5_EL1_Type_ETS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR5_EL1_Type_ETS r v)

def _set_ID_AA64MMFR1_EL1_Type_ETS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_ETS r v)

def _set_ID_MMFR5_Type_ETS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR5_Type_ETS r v)

def _set_ID_MMFR5_EL1_Type_nTLBPA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR5_EL1_Type_nTLBPA r v)

def _set_ID_AA64MMFR1_EL1_Type_nTLBPA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_nTLBPA r v)

def _set_ID_MMFR5_Type_nTLBPA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR5_Type_nTLBPA r v)

def _set_DBGCLAIMSET_EL1_Type_CLAIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGCLAIMSET_EL1_Type_CLAIM r v)

def _set_DBGCLAIMCLR_EL1_Type_CLAIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGCLAIMCLR_EL1_Type_CLAIM r v)

def _set_DBGCLAIMCLR_Type_CLAIM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGCLAIMCLR_Type_CLAIM r v)

def _set_DBGCLAIMSET_Type_CLAIM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGCLAIMSET_Type_CLAIM r v)

def _set_ICC_SRE_EL1_Type_DFB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL1_Type_DFB r v)

def _set_ICC_HSRE_Type_DFB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HSRE_Type_DFB r v)

def _set_ICC_MSRE_Type_DFB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MSRE_Type_DFB r v)

def _set_ICC_SRE_EL2_Type_DFB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL2_Type_DFB r v)

def _set_ICC_SRE_EL3_Type_DFB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL3_Type_DFB r v)

def _set_ICC_SRE_Type_DFB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_Type_DFB r v)

def _set_ICC_SRE_EL1_Type_DIB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL1_Type_DIB r v)

def _set_ICC_HSRE_Type_DIB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HSRE_Type_DIB r v)

def _set_ICC_MSRE_Type_DIB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MSRE_Type_DIB r v)

def _set_ICC_SRE_EL2_Type_DIB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL2_Type_DIB r v)

def _set_ICC_SRE_EL3_Type_DIB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL3_Type_DIB r v)

def _set_ICC_SRE_Type_DIB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_Type_DIB r v)

def _set_ICC_SRE_EL1_Type_SRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL1_Type_SRE r v)

def _set_ICC_HSRE_Type_SRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_HSRE_Type_SRE r v)

def _set_ICC_MSRE_Type_SRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MSRE_Type_SRE r v)

def _set_ICC_SRE_EL2_Type_SRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL2_Type_SRE r v)

def _set_ICC_SRE_EL3_Type_SRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_EL3_Type_SRE r v)

def _set_ICC_SRE_Type_SRE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_SRE_Type_SRE r v)

def _set_ID_ISAR4_EL1_Type_Barrier (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_EL1_Type_Barrier r v)

def _set_ID_ISAR4_Type_Barrier (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_Type_Barrier r v)

def _set_ID_ISAR4_EL1_Type_PSR_M (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_EL1_Type_PSR_M r v)

def _set_ID_ISAR4_Type_PSR_M (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_Type_PSR_M r v)

def _set_ID_ISAR4_EL1_Type_SMC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_EL1_Type_SMC r v)

def _set_ID_ISAR4_Type_SMC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_Type_SMC r v)

def _set_ID_ISAR4_EL1_Type_SWP_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_EL1_Type_SWP_frac r v)

def _set_ID_ISAR4_Type_SWP_frac (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_Type_SWP_frac r v)

def _set_ID_ISAR4_EL1_Type_SynchPrim_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_EL1_Type_SynchPrim_frac r v)

def _set_ID_ISAR4_Type_SynchPrim_frac (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_Type_SynchPrim_frac r v)

def _set_ID_ISAR4_EL1_Type_Unpriv (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_EL1_Type_Unpriv r v)

def _set_ID_ISAR4_Type_Unpriv (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_Type_Unpriv r v)

def _set_ID_ISAR4_EL1_Type_WithShifts (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_EL1_Type_WithShifts r v)

def _set_ID_ISAR4_Type_WithShifts (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_Type_WithShifts r v)

def _set_ID_ISAR4_EL1_Type_Writeback (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_EL1_Type_Writeback r v)

def _set_ID_ISAR4_Type_Writeback (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR4_Type_Writeback r v)

def _set_ID_ISAR1_EL1_Type_Endian (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_EL1_Type_Endian r v)

def _set_ID_ISAR1_Type_Endian (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_Type_Endian r v)

def _set_ID_ISAR1_EL1_Type_Except (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_EL1_Type_Except r v)

def _set_ID_ISAR1_Type_Except (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_Type_Except r v)

def _set_ID_ISAR1_EL1_Type_Except_AR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_EL1_Type_Except_AR r v)

def _set_ID_ISAR1_Type_Except_AR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_Type_Except_AR r v)

def _set_ID_ISAR1_EL1_Type_Extend (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_EL1_Type_Extend r v)

def _set_ID_ISAR1_Type_Extend (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_Type_Extend r v)

def _set_ID_ISAR1_EL1_Type_IfThen (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_EL1_Type_IfThen r v)

def _set_ID_ISAR1_Type_IfThen (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_Type_IfThen r v)

def _set_ID_ISAR1_EL1_Type_Immediate (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_EL1_Type_Immediate r v)

def _set_ID_ISAR1_Type_Immediate (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_Type_Immediate r v)

def _set_ID_ISAR1_EL1_Type_Interwork (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_EL1_Type_Interwork r v)

def _set_ID_ISAR1_Type_Interwork (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_Type_Interwork r v)

def _set_ID_ISAR1_EL1_Type_Jazelle (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_EL1_Type_Jazelle r v)

def _set_ID_ISAR1_Type_Jazelle (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR1_Type_Jazelle r v)

def _set_PMSELR_EL0_Type_SEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSELR_EL0_Type_SEL r v)

def _set_ERRSELR_EL1_Type_SEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRSELR_EL1_Type_SEL r v)

def _set_ERRSELR_Type_SEL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRSELR_Type_SEL r v)

def _set_PMSELR_Type_SEL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMSELR_Type_SEL r v)

def _set_ICC_CTLR_EL1_Type_A3V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL1_Type_A3V r v)

def _set_GICD_TYPER_Type_A3V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_A3V r v)

def _set_GICH_VTR_Type_A3V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VTR_Type_A3V r v)

def _set_ICC_CTLR_EL3_Type_A3V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_A3V r v)

def _set_ICC_CTLR_Type_A3V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_Type_A3V r v)

def _set_ICC_MCTLR_Type_A3V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_A3V r v)

def _set_ICH_VTR_EL2_Type_A3V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_A3V r v)

def _set_ICH_VTR_Type_A3V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_Type_A3V r v)

def _set_ICV_CTLR_EL1_Type_A3V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_EL1_Type_A3V r v)

def _set_ICV_CTLR_Type_A3V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_Type_A3V r v)

def _set_ICC_CTLR_EL1_Type_CBPR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL1_Type_CBPR r v)

def _set_GICC_CTLR_Type_CBPR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_CTLR_Type_CBPR r v)

def _set_GICV_CTLR_Type_CBPR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_CTLR_Type_CBPR r v)

def _set_ICC_CTLR_Type_CBPR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_Type_CBPR r v)

def _set_ICV_CTLR_EL1_Type_CBPR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_EL1_Type_CBPR r v)

def _set_ICV_CTLR_Type_CBPR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_Type_CBPR r v)

def _set_ICC_CTLR_EL1_Type_EOImode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL1_Type_EOImode r v)

def _set_GICC_CTLR_Type_EOImode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_CTLR_Type_EOImode r v)

def _set_GICV_CTLR_Type_EOImode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_CTLR_Type_EOImode r v)

def _set_ICC_CTLR_Type_EOImode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_Type_EOImode r v)

def _set_ICV_CTLR_EL1_Type_EOImode (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_EL1_Type_EOImode r v)

def _set_ICV_CTLR_Type_EOImode (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_Type_EOImode r v)

def _set_ICC_CTLR_EL1_Type_ExtRange (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL1_Type_ExtRange r v)

def _set_ICC_CTLR_EL3_Type_ExtRange (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_ExtRange r v)

def _set_ICC_CTLR_Type_ExtRange (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_Type_ExtRange r v)

def _set_ICC_MCTLR_Type_ExtRange (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_ExtRange r v)

def _set_ICV_CTLR_EL1_Type_ExtRange (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_EL1_Type_ExtRange r v)

def _set_ICV_CTLR_Type_ExtRange (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_Type_ExtRange r v)

def _set_ICC_CTLR_EL1_Type_IDbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL1_Type_IDbits r v)

def _set_GICD_TYPER_Type_IDbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_IDbits r v)

def _set_GICH_VTR_Type_IDbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VTR_Type_IDbits r v)

def _set_GICR_PROPBASER_Type_IDbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PROPBASER_Type_IDbits r v)

def _set_GICR_VPROPBASER_Type_IDbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_IDbits r v)

def _set_ICC_CTLR_EL3_Type_IDbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_IDbits r v)

def _set_ICC_CTLR_Type_IDbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_Type_IDbits r v)

def _set_ICC_MCTLR_Type_IDbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_IDbits r v)

def _set_ICH_VTR_EL2_Type_IDbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_IDbits r v)

def _set_ICH_VTR_Type_IDbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_Type_IDbits r v)

def _set_ICV_CTLR_EL1_Type_IDbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_EL1_Type_IDbits r v)

def _set_ICV_CTLR_Type_IDbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_Type_IDbits r v)

def _set_ICC_CTLR_EL1_Type_PMHE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL1_Type_PMHE r v)

def _set_ICC_CTLR_EL3_Type_PMHE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_PMHE r v)

def _set_ICC_CTLR_Type_PMHE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_Type_PMHE r v)

def _set_ICC_MCTLR_Type_PMHE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_PMHE r v)

def _set_ICC_CTLR_EL1_Type_PRIbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL1_Type_PRIbits r v)

def _set_GICH_VTR_Type_PRIbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VTR_Type_PRIbits r v)

def _set_ICC_CTLR_EL3_Type_PRIbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_PRIbits r v)

def _set_ICC_CTLR_Type_PRIbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_Type_PRIbits r v)

def _set_ICC_MCTLR_Type_PRIbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_PRIbits r v)

def _set_ICH_VTR_EL2_Type_PRIbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_PRIbits r v)

def _set_ICH_VTR_Type_PRIbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_Type_PRIbits r v)

def _set_ICV_CTLR_EL1_Type_PRIbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_EL1_Type_PRIbits r v)

def _set_ICV_CTLR_Type_PRIbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_Type_PRIbits r v)

def _set_ICC_CTLR_EL1_Type_RSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL1_Type_RSS r v)

def _set_GICD_TYPER_Type_RSS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_RSS r v)

def _set_ICC_CTLR_EL3_Type_RSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_RSS r v)

def _set_ICC_CTLR_Type_RSS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_Type_RSS r v)

def _set_ICC_MCTLR_Type_RSS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_RSS r v)

def _set_ICV_CTLR_EL1_Type_RSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_EL1_Type_RSS r v)

def _set_ICV_CTLR_Type_RSS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_Type_RSS r v)

def _set_ICC_CTLR_EL1_Type_SEIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL1_Type_SEIS r v)

def _set_GICH_VTR_Type_SEIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VTR_Type_SEIS r v)

def _set_GITS_TYPER_Type_SEIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_SEIS r v)

def _set_ICC_CTLR_EL3_Type_SEIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_SEIS r v)

def _set_ICC_CTLR_Type_SEIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_Type_SEIS r v)

def _set_ICC_MCTLR_Type_SEIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_SEIS r v)

def _set_ICH_VTR_EL2_Type_SEIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_SEIS r v)

def _set_ICH_VTR_Type_SEIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_Type_SEIS r v)

def _set_ICV_CTLR_EL1_Type_SEIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_EL1_Type_SEIS r v)

def _set_ICV_CTLR_Type_SEIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICV_CTLR_Type_SEIS r v)

def _set_ID_ISAR6_EL1_Type_CLRBHB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_CLRBHB r v)

def _set_ID_AA64ISAR2_EL1_Type_CLRBHB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_CLRBHB r v)

def _set_ID_ISAR6_Type_CLRBHB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR6_Type_CLRBHB r v)

/-- Type quantifiers: n : Int -/
def ICC_AP1R_EL1_read (n : Int) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_AP1R_EL1_Type ()) ) : SailM ICC_AP1R_EL1_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then
    (do
      sail_assert ((0 ≤b n) && (n <b 4)) "src/v8_base.sail:44767.45-44767.46"
      (pure (GetElem?.getElem! (← readReg ICC_AP1R_EL1_S) n)))
  else
    (do
      sail_assert ((0 ≤b n) && (n <b 4)) "src/v8_base.sail:44770.45-44770.46"
      (pure (GetElem?.getElem! (← readReg ICC_AP1R_EL1_NS) n)))

def _set_ICH_MISR_EL2_Type_EOI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_EL2_Type_EOI r v)

def _set_GICH_MISR_Type_EOI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_MISR_Type_EOI r v)

def _set_ICH_MISR_Type_EOI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_Type_EOI r v)

def _set_ICH_MISR_EL2_Type_LRENP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_EL2_Type_LRENP r v)

def _set_GICH_MISR_Type_LRENP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_MISR_Type_LRENP r v)

def _set_ICH_MISR_Type_LRENP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_Type_LRENP r v)

def _set_ICH_MISR_EL2_Type_NP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_EL2_Type_NP r v)

def _set_GICH_MISR_Type_NP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_MISR_Type_NP r v)

def _set_ICH_MISR_Type_NP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_Type_NP r v)

def _set_ICH_MISR_EL2_Type_VGrp0D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_EL2_Type_VGrp0D r v)

def _set_GICH_MISR_Type_VGrp0D (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_MISR_Type_VGrp0D r v)

def _set_ICH_MISR_Type_VGrp0D (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_Type_VGrp0D r v)

def _set_ICH_MISR_EL2_Type_VGrp0E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_EL2_Type_VGrp0E r v)

def _set_GICH_MISR_Type_VGrp0E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_MISR_Type_VGrp0E r v)

def _set_ICH_MISR_Type_VGrp0E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_Type_VGrp0E r v)

def _set_ICH_MISR_EL2_Type_VGrp1D (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_EL2_Type_VGrp1D r v)

def _set_GICH_MISR_Type_VGrp1D (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_MISR_Type_VGrp1D r v)

def _set_ICH_MISR_Type_VGrp1D (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_Type_VGrp1D r v)

def _set_ICH_MISR_EL2_Type_VGrp1E (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_EL2_Type_VGrp1E r v)

def _set_GICH_MISR_Type_VGrp1E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_MISR_Type_VGrp1E r v)

def _set_ICH_MISR_Type_VGrp1E (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_MISR_Type_VGrp1E r v)

def _set_CSSELR_EL1_Type_InD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CSSELR_EL1_Type_InD r v)

def _set_CSSELR_Type_InD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CSSELR_Type_InD r v)

def _set_CSSELR_EL1_Type_Level (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CSSELR_EL1_Type_Level r v)

def _set_CSSELR_Type_Level (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CSSELR_Type_Level r v)

def _set_CSSELR_EL1_Type_TnD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CSSELR_EL1_Type_TnD r v)

def _set_ISR_EL1_Type_IS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ISR_EL1_Type_IS r v)

def _set_ID_ISAR3_EL1_Type_SIMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_EL1_Type_SIMD r v)

def _set_ID_ISAR3_Type_SIMD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_Type_SIMD r v)

def _set_ID_ISAR3_EL1_Type_SVC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_EL1_Type_SVC r v)

def _set_ID_ISAR3_Type_SVC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_Type_SVC r v)

def _set_ID_ISAR3_EL1_Type_Saturate (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_EL1_Type_Saturate r v)

def _set_ID_ISAR3_Type_Saturate (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_Type_Saturate r v)

def _set_ID_ISAR3_EL1_Type_SynchPrim (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_EL1_Type_SynchPrim r v)

def _set_ID_ISAR3_Type_SynchPrim (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_Type_SynchPrim r v)

def _set_ID_ISAR3_EL1_Type_T32Copy (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_EL1_Type_T32Copy r v)

def _set_ID_ISAR3_Type_T32Copy (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_Type_T32Copy r v)

def _set_ID_ISAR3_EL1_Type_T32EE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_EL1_Type_T32EE r v)

def _set_ID_ISAR3_Type_T32EE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_Type_T32EE r v)

def _set_ID_ISAR3_EL1_Type_TabBranch (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_EL1_Type_TabBranch r v)

def _set_ID_ISAR3_Type_TabBranch (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_Type_TabBranch r v)

def _set_ID_ISAR3_EL1_Type_TrueNOP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_EL1_Type_TrueNOP r v)

def _set_ID_ISAR3_Type_TrueNOP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR3_Type_TrueNOP r v)

def _set_MECIDR_EL2_Type_MECIDWidthm1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MECIDR_EL2_Type_MECIDWidthm1 r v)

def _set_SMIDR_EL1_Type_Affinity (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMIDR_EL1_Type_Affinity r v)

def _set_SMIDR_EL1_Type_SMPS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_SMIDR_EL1_Type_SMPS r v)

def _set_HFGWTR_EL2_Type_AFSR0_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_AFSR0_EL1 r v)

def _set_HFGRTR_EL2_Type_AFSR0_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_AFSR0_EL1 r v)

def _set_HFGWTR_EL2_Type_AFSR1_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_AFSR1_EL1 r v)

def _set_HFGRTR_EL2_Type_AFSR1_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_AFSR1_EL1 r v)

def _set_HFGWTR_EL2_Type_AMAIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_AMAIR_EL1 r v)

def _set_HFGRTR_EL2_Type_AMAIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_AMAIR_EL1 r v)

def _set_HFGWTR_EL2_Type_APDAKey (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_APDAKey r v)

def _set_HFGRTR_EL2_Type_APDAKey (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_APDAKey r v)

def _set_HFGWTR_EL2_Type_APDBKey (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_APDBKey r v)

def _set_HFGRTR_EL2_Type_APDBKey (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_APDBKey r v)

def _set_HFGWTR_EL2_Type_APGAKey (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_APGAKey r v)

def _set_HFGRTR_EL2_Type_APGAKey (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_APGAKey r v)

def _set_HFGWTR_EL2_Type_APIAKey (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_APIAKey r v)

def _set_HFGRTR_EL2_Type_APIAKey (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_APIAKey r v)

def _set_HFGWTR_EL2_Type_APIBKey (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_APIBKey r v)

def _set_HFGRTR_EL2_Type_APIBKey (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_APIBKey r v)

def _set_HFGWTR_EL2_Type_CONTEXTIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_CONTEXTIDR_EL1 r v)

def _set_HFGRTR_EL2_Type_CONTEXTIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_CONTEXTIDR_EL1 r v)

def _set_PMVCIDSR_Type_CONTEXTIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMVCIDSR_Type_CONTEXTIDR_EL1 r v)

def _set_HFGWTR_EL2_Type_CPACR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_CPACR_EL1 r v)

def _set_HFGRTR_EL2_Type_CPACR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_CPACR_EL1 r v)

def _set_HFGWTR_EL2_Type_CSSELR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_CSSELR_EL1 r v)

def _set_HFGRTR_EL2_Type_CSSELR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_CSSELR_EL1 r v)

def _set_HFGWTR_EL2_Type_ERRSELR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ERRSELR_EL1 r v)

def _set_HFGRTR_EL2_Type_ERRSELR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERRSELR_EL1 r v)

def _set_HFGWTR_EL2_Type_ERXADDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ERXADDR_EL1 r v)

def _set_HFGRTR_EL2_Type_ERXADDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXADDR_EL1 r v)

def _set_HFGWTR_EL2_Type_ERXCTLR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ERXCTLR_EL1 r v)

def _set_HFGRTR_EL2_Type_ERXCTLR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXCTLR_EL1 r v)

def _set_HFGWTR_EL2_Type_ERXMISCn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ERXMISCn_EL1 r v)

def _set_HFGRTR_EL2_Type_ERXMISCn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXMISCn_EL1 r v)

def _set_HFGWTR_EL2_Type_ERXPFGCDN_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ERXPFGCDN_EL1 r v)

def _set_HFGRTR_EL2_Type_ERXPFGCDN_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXPFGCDN_EL1 r v)

def _set_HFGWTR_EL2_Type_ERXPFGCTL_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ERXPFGCTL_EL1 r v)

def _set_HFGRTR_EL2_Type_ERXPFGCTL_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXPFGCTL_EL1 r v)

def _set_HFGWTR_EL2_Type_ERXSTATUS_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ERXSTATUS_EL1 r v)

def _set_HFGRTR_EL2_Type_ERXSTATUS_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXSTATUS_EL1 r v)

def _set_HFGWTR_EL2_Type_ESR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ESR_EL1 r v)

def _set_HFGRTR_EL2_Type_ESR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ESR_EL1 r v)

def _set_HFGWTR_EL2_Type_FAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_FAR_EL1 r v)

def _set_HFGRTR_EL2_Type_FAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_FAR_EL1 r v)

def _set_HFGWTR_EL2_Type_ICC_IGRPENn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ICC_IGRPENn_EL1 r v)

def _set_HFGRTR_EL2_Type_ICC_IGRPENn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ICC_IGRPENn_EL1 r v)

def _set_HFGWTR_EL2_Type_LORC_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_LORC_EL1 r v)

def _set_HFGRTR_EL2_Type_LORC_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_LORC_EL1 r v)

def _set_HFGWTR_EL2_Type_LOREA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_LOREA_EL1 r v)

def _set_HFGRTR_EL2_Type_LOREA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_LOREA_EL1 r v)

def _set_HFGWTR_EL2_Type_LORN_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_LORN_EL1 r v)

def _set_HFGRTR_EL2_Type_LORN_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_LORN_EL1 r v)

def _set_HFGWTR_EL2_Type_LORSA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_LORSA_EL1 r v)

def _set_HFGRTR_EL2_Type_LORSA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_LORSA_EL1 r v)

def _set_HFGWTR_EL2_Type_MAIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_MAIR_EL1 r v)

def _set_HFGRTR_EL2_Type_MAIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_MAIR_EL1 r v)

def _set_HFGWTR_EL2_Type_PAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_PAR_EL1 r v)

def _set_HFGRTR_EL2_Type_PAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_PAR_EL1 r v)

def _set_HFGWTR_EL2_Type_SCTLR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_SCTLR_EL1 r v)

def _set_HFGRTR_EL2_Type_SCTLR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_SCTLR_EL1 r v)

def _set_HFGWTR_EL2_Type_SCXTNUM_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_SCXTNUM_EL0 r v)

def _set_HFGRTR_EL2_Type_SCXTNUM_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_SCXTNUM_EL0 r v)

def _set_HFGWTR_EL2_Type_SCXTNUM_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_SCXTNUM_EL1 r v)

def _set_HFGRTR_EL2_Type_SCXTNUM_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_SCXTNUM_EL1 r v)

def _set_HFGWTR_EL2_Type_TCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TCR_EL1 r v)

def _set_HFGRTR_EL2_Type_TCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TCR_EL1 r v)

def _set_HFGWTR_EL2_Type_TPIDRRO_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TPIDRRO_EL0 r v)

def _set_HFGRTR_EL2_Type_TPIDRRO_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TPIDRRO_EL0 r v)

def _set_HFGWTR_EL2_Type_TPIDR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TPIDR_EL0 r v)

def _set_HFGRTR_EL2_Type_TPIDR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TPIDR_EL0 r v)

def _set_HFGWTR_EL2_Type_TPIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TPIDR_EL1 r v)

def _set_HFGRTR_EL2_Type_TPIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TPIDR_EL1 r v)

def _set_HFGWTR_EL2_Type_TTBR0_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TTBR0_EL1 r v)

def _set_HFGRTR_EL2_Type_TTBR0_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TTBR0_EL1 r v)

def _set_HFGWTR_EL2_Type_TTBR1_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TTBR1_EL1 r v)

def _set_HFGRTR_EL2_Type_TTBR1_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TTBR1_EL1 r v)

def _set_HFGWTR_EL2_Type_VBAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_VBAR_EL1 r v)

def _set_HFGRTR_EL2_Type_VBAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_VBAR_EL1 r v)

def _set_HFGWTR_EL2_Type_nACCDATA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nACCDATA_EL1 r v)

def _set_HFGRTR_EL2_Type_nACCDATA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nACCDATA_EL1 r v)

def _set_HFGWTR_EL2_Type_nAMAIR2_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nAMAIR2_EL1 r v)

def _set_HFGRTR_EL2_Type_nAMAIR2_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nAMAIR2_EL1 r v)

def _set_HFGWTR_EL2_Type_nGCS_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nGCS_EL0 r v)

def _set_HFGRTR_EL2_Type_nGCS_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nGCS_EL0 r v)

def _set_HFGWTR_EL2_Type_nGCS_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nGCS_EL1 r v)

def _set_HFGRTR_EL2_Type_nGCS_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nGCS_EL1 r v)

def _set_HFGWTR_EL2_Type_nMAIR2_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nMAIR2_EL1 r v)

def _set_HFGRTR_EL2_Type_nMAIR2_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nMAIR2_EL1 r v)

def _set_HFGWTR_EL2_Type_nPIRE0_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nPIRE0_EL1 r v)

def _set_HFGRTR_EL2_Type_nPIRE0_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nPIRE0_EL1 r v)

def _set_HFGWTR_EL2_Type_nPIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nPIR_EL1 r v)

def _set_HFGRTR_EL2_Type_nPIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nPIR_EL1 r v)

def _set_HFGWTR_EL2_Type_nPOR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nPOR_EL0 r v)

def _set_HFGRTR_EL2_Type_nPOR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nPOR_EL0 r v)

def _set_HFGWTR_EL2_Type_nPOR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nPOR_EL1 r v)

def _set_HFGRTR_EL2_Type_nPOR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nPOR_EL1 r v)

def _set_HFGWTR_EL2_Type_nRCWMASK_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nRCWMASK_EL1 r v)

def _set_HFGRTR_EL2_Type_nRCWMASK_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nRCWMASK_EL1 r v)

def _set_HFGWTR_EL2_Type_nS2POR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nS2POR_EL1 r v)

def _set_HFGRTR_EL2_Type_nS2POR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nS2POR_EL1 r v)

def _set_HFGWTR_EL2_Type_nSMPRI_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nSMPRI_EL1 r v)

def _set_HFGRTR_EL2_Type_nSMPRI_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nSMPRI_EL1 r v)

def _set_HFGWTR_EL2_Type_nTPIDR2_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nTPIDR2_EL0 r v)

def _set_HFGRTR_EL2_Type_nTPIDR2_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nTPIDR2_EL0 r v)

def _set_PMUSERENR_EL0_Type_CR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_CR r v)

def _set_PMUSERENR_Type_CR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_Type_CR r v)

def _set_PMUSERENR_EL0_Type_ER (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_ER r v)

def _set_PMUSERENR_Type_ER (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_Type_ER r v)

def _set_PMUSERENR_EL0_Type_IR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_IR r v)

def _set_GICR_CTLR_Type_IR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CTLR_Type_IR r v)

def _set_PMUSERENR_EL0_Type_TID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_TID r v)

def _set_PMUSERENR_Type_TID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_Type_TID r v)

def _set_PMUSERENR_EL0_Type_UEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_UEN r v)

def _set_PMCFGR_Type_UEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_UEN r v)

def __set_FPEXC32_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : FPEXC32_EL2_Type := value_name
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange (← readReg FPEXC32_EL2) 6 5 (BitVec.slice r 5 2))
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange (← readReg FPEXC32_EL2) 30 8 (BitVec.slice r 8 23))
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange (← readReg FPEXC32_EL2) 63 32 (BitVec.slice r 32 32))
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions")))) : Bool)
  then writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange (← readReg FPEXC32_EL2) 7 7 (_get_FPEXC32_EL2_Type_IDF r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions")))) : Bool)
  then writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange (← readReg FPEXC32_EL2) 4 4 (_get_FPEXC32_EL2_Type_IXF r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions")))) : Bool)
  then writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange (← readReg FPEXC32_EL2) 3 3 (_get_FPEXC32_EL2_Type_UFF r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions")))) : Bool)
  then writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange (← readReg FPEXC32_EL2) 2 2 (_get_FPEXC32_EL2_Type_OFF r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions")))) : Bool)
  then writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange (← readReg FPEXC32_EL2) 1 1 (_get_FPEXC32_EL2_Type_DZF r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions")))) : Bool)
  then writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange (← readReg FPEXC32_EL2) 0 0 (_get_FPEXC32_EL2_Type_IOF r))
  else (pure ())

def _set_ID_PFR0_EL1_Type_State0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_State0 r v)

def _set_ID_PFR0_Type_State0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_Type_State0 r v)

def _set_ID_PFR0_EL1_Type_State1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_State1 r v)

def _set_ID_PFR0_Type_State1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_Type_State1 r v)

def _set_ID_PFR0_EL1_Type_State2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_State2 r v)

def _set_ID_PFR0_Type_State2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_Type_State2 r v)

def _set_ID_PFR0_EL1_Type_State3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_State3 r v)

def _set_ID_PFR0_Type_State3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR0_Type_State3 r v)

def _set_MVFR1_EL1_Type_FPDNaN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_EL1_Type_FPDNaN r v)

def _set_MVFR1_Type_FPDNaN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_Type_FPDNaN r v)

def _set_MVFR1_EL1_Type_FPFtZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_EL1_Type_FPFtZ r v)

def _set_MVFR1_Type_FPFtZ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_Type_FPFtZ r v)

def _set_MVFR1_EL1_Type_FPHP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_EL1_Type_FPHP r v)

def _set_MVFR1_Type_FPHP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_Type_FPHP r v)

def _set_MVFR1_EL1_Type_SIMDFMAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_EL1_Type_SIMDFMAC r v)

def _set_MVFR1_Type_SIMDFMAC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_Type_SIMDFMAC r v)

def _set_MVFR1_EL1_Type_SIMDHP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_EL1_Type_SIMDHP r v)

def _set_MVFR1_Type_SIMDHP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_Type_SIMDHP r v)

def _set_MVFR1_EL1_Type_SIMDInt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_EL1_Type_SIMDInt r v)

def _set_MVFR1_Type_SIMDInt (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_Type_SIMDInt r v)

def _set_MVFR1_EL1_Type_SIMDLS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_EL1_Type_SIMDLS r v)

def _set_MVFR1_Type_SIMDLS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_Type_SIMDLS r v)

def _set_MVFR1_EL1_Type_SIMDSP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_EL1_Type_SIMDSP r v)

def _set_MVFR1_Type_SIMDSP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR1_Type_SIMDSP r v)

def _set_HDFGWTR2_EL2_Type_nMDSELR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nMDSELR_EL1 r v)

def _set_HDFGRTR2_EL2_Type_nMDSELR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nMDSELR_EL1 r v)

def _set_HDFGWTR2_EL2_Type_nPMECR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMECR_EL1 r v)

def _set_HDFGRTR2_EL2_Type_nPMECR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMECR_EL1 r v)

def _set_HDFGWTR2_EL2_Type_nPMIAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMIAR_EL1 r v)

def _set_HDFGRTR2_EL2_Type_nPMIAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMIAR_EL1 r v)

def _set_HDFGWTR2_EL2_Type_nPMICFILTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMICFILTR_EL0 r v)

def _set_HDFGRTR2_EL2_Type_nPMICFILTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMICFILTR_EL0 r v)

def _set_HDFGWTR2_EL2_Type_nPMICNTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMICNTR_EL0 r v)

def _set_HDFGRTR2_EL2_Type_nPMICNTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMICNTR_EL0 r v)

def _set_HDFGWTR2_EL2_Type_nPMSDSFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMSDSFR_EL1 r v)

def _set_HDFGRTR2_EL2_Type_nPMSDSFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMSDSFR_EL1 r v)

def _set_HDFGWTR2_EL2_Type_nPMSSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMSSCR_EL1 r v)

def _set_HDFGRTR2_EL2_Type_nPMSSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMSSCR_EL1 r v)

def _set_HDFGWTR2_EL2_Type_nPMUACR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMUACR_EL1 r v)

def _set_HDFGRTR2_EL2_Type_nPMUACR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMUACR_EL1 r v)

def _set_HDFGWTR2_EL2_Type_nPMZR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMZR_EL0 r v)

def _set_HDFGWTR2_EL2_Type_nSPMACCESSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMACCESSR_EL1 r v)

def _set_HDFGRTR2_EL2_Type_nSPMACCESSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMACCESSR_EL1 r v)

def _set_HDFGWTR2_EL2_Type_nSPMCNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMCNTEN r v)

def _set_HDFGRTR2_EL2_Type_nSPMCNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMCNTEN r v)

def _set_HDFGWTR2_EL2_Type_nSPMCR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMCR_EL0 r v)

def _set_HDFGRTR2_EL2_Type_nSPMCR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMCR_EL0 r v)

def _set_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 r v)

def _set_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 r v)

def _set_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 r v)

def _set_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 r v)

def _set_HDFGWTR2_EL2_Type_nSPMINTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMINTEN r v)

def _set_HDFGRTR2_EL2_Type_nSPMINTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMINTEN r v)

def _set_HDFGWTR2_EL2_Type_nSPMOVS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMOVS r v)

def _set_HDFGRTR2_EL2_Type_nSPMOVS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMOVS r v)

def _set_HDFGWTR2_EL2_Type_nSPMSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMSCR_EL1 r v)

def _set_HDFGRTR2_EL2_Type_nSPMSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMSCR_EL1 r v)

def _set_HDFGWTR2_EL2_Type_nSPMSELR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMSELR_EL0 r v)

def _set_HDFGRTR2_EL2_Type_nSPMSELR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMSELR_EL0 r v)

def _set_ID_ISAR0_EL1_Type_BitCount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_BitCount r v)

def _set_ID_ISAR0_Type_BitCount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_Type_BitCount r v)

def _set_ID_ISAR0_EL1_Type_BitField (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_BitField r v)

def _set_ID_ISAR0_Type_BitField (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_Type_BitField r v)

def _set_ID_ISAR0_EL1_Type_CmpBranch (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_CmpBranch r v)

def _set_ID_ISAR0_Type_CmpBranch (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_Type_CmpBranch r v)

def _set_ID_ISAR0_EL1_Type_Coproc (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_Coproc r v)

def _set_ID_ISAR0_Type_Coproc (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_Type_Coproc r v)

def _set_ID_ISAR0_EL1_Type_Debug (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_Debug r v)

def _set_ID_ISAR0_Type_Debug (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_Type_Debug r v)

def _set_ID_ISAR0_EL1_Type_Divide (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_Divide r v)

def _set_ID_ISAR0_Type_Divide (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_Type_Divide r v)

def _set_ID_ISAR0_EL1_Type_Swap (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_Swap r v)

def _set_ID_ISAR0_Type_Swap (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR0_Type_Swap r v)

def __get_selected_SPMACCESSR_EL2_field (_ : Unit) : SailM (BitVec 2) := do
  let idx ← do (pure ((BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) *i 2))
  (pure (BitVec.slice (← readReg SPMACCESSR_EL2) idx 2))

def _set_MDRAR_EL1_Type_ROMADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 44)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDRAR_EL1_Type_ROMADDR r v)

def _set_DBGDRAR_Type_ROMADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 36)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDRAR_Type_ROMADDR r v)

def _set_MDRAR_EL1_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MDRAR_EL1_Type_Valid r v)

def _set_DBGDRAR_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDRAR_Type_Valid r v)

def _set_GICM_TYPER_Type_Valid (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_TYPER_Type_Valid r v)

def _set_GICR_VPENDBASER_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_Valid r v)

def _set_GICR_VPROPBASER_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Valid r v)

def _set_GITS_CBASER_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CBASER_Type_Valid r v)

def _set_LORSA_EL1_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORSA_EL1_Type_Valid r v)

def _set_ICC_IGRPEN1_EL3_Type_EnableGrp1NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN1_EL3_Type_EnableGrp1NS r v)

def _set_GICD_CTLR_Type_EnableGrp1NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_EnableGrp1NS r v)

def _set_ICC_MGRPEN1_Type_EnableGrp1NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MGRPEN1_Type_EnableGrp1NS r v)

def _set_ICC_IGRPEN1_EL3_Type_EnableGrp1S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_IGRPEN1_EL3_Type_EnableGrp1S r v)

def _set_GICD_CTLR_Type_EnableGrp1S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_EnableGrp1S r v)

def _set_ICC_MGRPEN1_Type_EnableGrp1S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MGRPEN1_Type_EnableGrp1S r v)

def _set_ID_MMFR1_EL1_Type_BPred (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_BPred r v)

def _set_ID_MMFR1_Type_BPred (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_Type_BPred r v)

def _set_ID_MMFR1_EL1_Type_L1Hvd (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1Hvd r v)

def _set_ID_MMFR1_Type_L1Hvd (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1Hvd r v)

def _set_ID_MMFR1_EL1_Type_L1HvdSW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1HvdSW r v)

def _set_ID_MMFR1_Type_L1HvdSW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1HvdSW r v)

def _set_ID_MMFR1_EL1_Type_L1HvdVA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1HvdVA r v)

def _set_ID_MMFR1_Type_L1HvdVA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1HvdVA r v)

def _set_ID_MMFR1_EL1_Type_L1TstCln (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1TstCln r v)

def _set_ID_MMFR1_Type_L1TstCln (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1TstCln r v)

def _set_ID_MMFR1_EL1_Type_L1Uni (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1Uni r v)

def _set_ID_MMFR1_Type_L1Uni (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1Uni r v)

def _set_ID_MMFR1_EL1_Type_L1UniSW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1UniSW r v)

def _set_ID_MMFR1_Type_L1UniSW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1UniSW r v)

def _set_ID_MMFR1_EL1_Type_L1UniVA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1UniVA r v)

def _set_ID_MMFR1_Type_L1UniVA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1UniVA r v)

def _set_ID_AA64MMFR1_EL1_Type_AFP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_AFP r v)

def _set_ID_AA64MMFR1_EL1_Type_ECBHB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_ECBHB r v)

def _set_ID_AA64MMFR1_EL1_Type_HAFDBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_HAFDBS r v)

def _set_ID_AA64MMFR1_EL1_Type_HCX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_HCX r v)

def _set_ID_AA64MMFR1_EL1_Type_LO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_LO r v)

def _set_ID_AA64MMFR1_EL1_Type_TIDCP1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_TIDCP1 r v)

def _set_ID_AA64MMFR1_EL1_Type_TWED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_TWED r v)

def _set_ID_AA64MMFR1_EL1_Type_VH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_VH r v)

def _set_ID_AA64MMFR1_EL1_Type_VMIDBits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_VMIDBits r v)

def _set_ID_MMFR0_EL1_Type_AuxReg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_AuxReg r v)

def _set_ID_MMFR0_Type_AuxReg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_Type_AuxReg r v)

def _set_ID_MMFR0_EL1_Type_FCSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_FCSE r v)

def _set_ID_MMFR0_Type_FCSE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_Type_FCSE r v)

def _set_ID_MMFR0_EL1_Type_InnerShr (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_InnerShr r v)

def _set_ID_MMFR0_Type_InnerShr (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_Type_InnerShr r v)

def _set_ID_MMFR0_EL1_Type_OuterShr (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_OuterShr r v)

def _set_ID_MMFR0_Type_OuterShr (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_Type_OuterShr r v)

def _set_ID_MMFR0_EL1_Type_PMSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_PMSA r v)

def _set_EDAA32PFR_Type_PMSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDAA32PFR_Type_PMSA r v)

def _set_ID_MMFR0_Type_PMSA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_Type_PMSA r v)

def _set_ID_MMFR0_EL1_Type_ShareLvl (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_ShareLvl r v)

def _set_ID_MMFR0_Type_ShareLvl (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_Type_ShareLvl r v)

def _set_ID_MMFR0_EL1_Type_TCM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_TCM r v)

def _set_ID_MMFR0_Type_TCM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_Type_TCM r v)

def _set_ID_MMFR0_EL1_Type_VMSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_VMSA r v)

def _set_EDAA32PFR_Type_VMSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDAA32PFR_Type_VMSA r v)

def _set_ID_MMFR0_Type_VMSA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR0_Type_VMSA r v)

def _set_ICH_VMCR_EL2_Type_VAckCtl (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VAckCtl r v)

def _set_GICH_VMCR_Type_VAckCtl (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VMCR_Type_VAckCtl r v)

def _set_ICH_VMCR_Type_VAckCtl (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_Type_VAckCtl r v)

def _set_ICH_VMCR_EL2_Type_VBPR0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VBPR0 r v)

def _set_GICH_VMCR_Type_VBPR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VMCR_Type_VBPR0 r v)

def _set_ICH_VMCR_Type_VBPR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_Type_VBPR0 r v)

def _set_ICH_VMCR_EL2_Type_VBPR1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VBPR1 r v)

def _set_GICH_VMCR_Type_VBPR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VMCR_Type_VBPR1 r v)

def _set_ICH_VMCR_Type_VBPR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_Type_VBPR1 r v)

def _set_ICH_VMCR_EL2_Type_VCBPR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VCBPR r v)

def _set_GICH_VMCR_Type_VCBPR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VMCR_Type_VCBPR r v)

def _set_ICH_VMCR_Type_VCBPR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_Type_VCBPR r v)

def _set_ICH_VMCR_EL2_Type_VENG0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VENG0 r v)

def _set_GICH_VMCR_Type_VENG0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VMCR_Type_VENG0 r v)

def _set_ICH_VMCR_Type_VENG0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_Type_VENG0 r v)

def _set_ICH_VMCR_EL2_Type_VENG1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VENG1 r v)

def _set_GICH_VMCR_Type_VENG1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VMCR_Type_VENG1 r v)

def _set_ICH_VMCR_Type_VENG1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_Type_VENG1 r v)

def _set_ICH_VMCR_EL2_Type_VEOIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VEOIM r v)

def _set_GICH_VMCR_Type_VEOIM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VMCR_Type_VEOIM r v)

def _set_ICH_VMCR_Type_VEOIM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_Type_VEOIM r v)

def _set_ICH_VMCR_EL2_Type_VFIQEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VFIQEn r v)

def _set_GICH_VMCR_Type_VFIQEn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VMCR_Type_VFIQEn r v)

def _set_ICH_VMCR_Type_VFIQEn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_Type_VFIQEn r v)

def _set_ICH_VMCR_EL2_Type_VPMR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VPMR r v)

def _set_GICH_VMCR_Type_VPMR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VMCR_Type_VPMR r v)

def _set_ICH_VMCR_Type_VPMR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VMCR_Type_VPMR r v)

def _set_ICC_CTLR_EL3_Type_CBPR_EL1NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_CBPR_EL1NS r v)

def _set_ICC_MCTLR_Type_CBPR_EL1NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_CBPR_EL1NS r v)

def _set_ICC_CTLR_EL3_Type_CBPR_EL1S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_CBPR_EL1S r v)

def _set_ICC_MCTLR_Type_CBPR_EL1S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_CBPR_EL1S r v)

def _set_ICC_CTLR_EL3_Type_EOImode_EL1NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_EOImode_EL1NS r v)

def _set_ICC_MCTLR_Type_EOImode_EL1NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_EOImode_EL1NS r v)

def _set_ICC_CTLR_EL3_Type_EOImode_EL1S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_EOImode_EL1S r v)

def _set_ICC_MCTLR_Type_EOImode_EL1S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_EOImode_EL1S r v)

def _set_ICC_CTLR_EL3_Type_EOImode_EL3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_EOImode_EL3 r v)

def _set_ICC_MCTLR_Type_EOImode_EL3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_EOImode_EL3 r v)

def _set_ICC_CTLR_EL3_Type_RM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_RM r v)

def _set_ICC_MCTLR_Type_RM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_RM r v)

def _set_ICC_CTLR_EL3_Type_nDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_nDS r v)

def _set_ICC_MCTLR_Type_nDS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICC_MCTLR_Type_nDS r v)

def __set_SCTLR_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : SCTLR_EL2_Type := value_name
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 6 0 (BitVec.slice r 0 7))
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 63 8 (BitVec.slice r 8 56))
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_ITD")))) : Bool)
  then writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 7 7 (_get_SCTLR_EL2_Type_ITD r))
  else (pure ())

def _set_ID_AA64PFR2_EL1_Type_MTEFAR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR2_EL1_Type_MTEFAR r v)

def _set_ID_AA64PFR2_EL1_Type_MTEPERM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR2_EL1_Type_MTEPERM r v)

def _set_ID_AA64PFR2_EL1_Type_MTESTOREONLY (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64PFR2_EL1_Type_MTESTOREONLY r v)

def _set_CCSIDR2_EL1_Type_NumSets (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR2_EL1_Type_NumSets r v)

def _set_CCSIDR2_Type_NumSets (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR2_Type_NumSets r v)

def _set_CCSIDR_Type_NumSets (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 15)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR_Type_NumSets r v)

def _set_ID_AA64ISAR2_EL1_Type_APA3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_APA3 r v)

def _set_ID_AA64ISAR2_EL1_Type_BC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_BC r v)

def _set_ID_AA64ISAR2_EL1_Type_CSSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_CSSC r v)

def _set_ID_AA64ISAR2_EL1_Type_GPA3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_GPA3 r v)

def _set_ID_AA64ISAR2_EL1_Type_MOPS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_MOPS r v)

def _set_ID_AA64ISAR2_EL1_Type_PAC_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_PAC_frac r v)

def _set_ID_AA64ISAR2_EL1_Type_PRFMSLC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_PRFMSLC r v)

def _set_ID_AA64ISAR2_EL1_Type_RPRES (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_RPRES r v)

def _set_ID_AA64ISAR2_EL1_Type_RPRFM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_RPRFM r v)

def _set_ID_AA64ISAR2_EL1_Type_SYSINSTR_128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_SYSINSTR_128 r v)

def _set_ID_AA64ISAR2_EL1_Type_SYSREG_128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_SYSREG_128 r v)

def _set_ID_AA64ISAR2_EL1_Type_WFxT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_WFxT r v)

def _set_HFGRTR2_EL2_Type_nERXGSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR2_EL2_Type_nERXGSR_EL1 r v)

def _set_HFGRTR2_EL2_Type_nPFAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR2_EL2_Type_nPFAR_EL1 r v)

def _set_HFGWTR2_EL2_Type_nPFAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR2_EL2_Type_nPFAR_EL1 r v)

def _set_HFGRTR2_EL2_Type_nRCWSMASK_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR2_EL2_Type_nRCWSMASK_EL1 r v)

def _set_HFGWTR2_EL2_Type_nRCWSMASK_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGWTR2_EL2_Type_nRCWSMASK_EL1 r v)

def _set_ID_ISAR5_EL1_Type_SEVL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_EL1_Type_SEVL r v)

def _set_ID_ISAR5_Type_SEVL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_Type_SEVL r v)

def _set_ID_ISAR5_EL1_Type_VCMA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_EL1_Type_VCMA r v)

def _set_ID_ISAR5_Type_VCMA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_ISAR5_Type_VCMA r v)

def _set_ICH_HCR_EL2_Type_DVIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_DVIM r v)

def _set_ICH_VTR_EL2_Type_DVIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_DVIM r v)

def _set_ICH_HCR_EL2_Type_EOIcount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_EOIcount r v)

def _set_ICH_HCR_Type_EOIcount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_EOIcount r v)

def _set_ICH_HCR_EL2_Type_En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_En r v)

def _set_GICH_HCR_Type_En (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_HCR_Type_En r v)

def _set_ICH_HCR_Type_En (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_En r v)

def _set_ICH_HCR_EL2_Type_LRENPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_LRENPIE r v)

def _set_GICH_HCR_Type_LRENPIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_HCR_Type_LRENPIE r v)

def _set_ICH_HCR_Type_LRENPIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_LRENPIE r v)

def _set_ICH_HCR_EL2_Type_NPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_NPIE r v)

def _set_GICH_HCR_Type_NPIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_HCR_Type_NPIE r v)

def _set_ICH_HCR_Type_NPIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_NPIE r v)

def _set_ICH_HCR_EL2_Type_TALL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_TALL0 r v)

def _set_ICH_HCR_Type_TALL0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_TALL0 r v)

def _set_ICH_HCR_EL2_Type_TALL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_TALL1 r v)

def _set_ICH_HCR_Type_TALL1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_TALL1 r v)

def _set_ICH_HCR_EL2_Type_TDIR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_TDIR r v)

def _set_ICH_HCR_Type_TDIR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_TDIR r v)

def _set_ICH_HCR_EL2_Type_TSEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_TSEI r v)

def _set_ICH_HCR_Type_TSEI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_TSEI r v)

def _set_ICH_HCR_EL2_Type_UIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_UIE r v)

def _set_GICH_HCR_Type_UIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_HCR_Type_UIE r v)

def _set_ICH_HCR_Type_UIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_UIE r v)

def _set_ICH_HCR_EL2_Type_VGrp0DIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_VGrp0DIE r v)

def _set_GICH_HCR_Type_VGrp0DIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_HCR_Type_VGrp0DIE r v)

def _set_ICH_HCR_Type_VGrp0DIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_VGrp0DIE r v)

def _set_ICH_HCR_EL2_Type_VGrp0EIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_VGrp0EIE r v)

def _set_GICH_HCR_Type_VGrp0EIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_HCR_Type_VGrp0EIE r v)

def _set_ICH_HCR_Type_VGrp0EIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_VGrp0EIE r v)

def _set_ICH_HCR_EL2_Type_VGrp1DIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_VGrp1DIE r v)

def _set_GICH_HCR_Type_VGrp1DIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_HCR_Type_VGrp1DIE r v)

def _set_ICH_HCR_Type_VGrp1DIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_VGrp1DIE r v)

def _set_ICH_HCR_EL2_Type_VGrp1EIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_VGrp1EIE r v)

def _set_GICH_HCR_Type_VGrp1EIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_HCR_Type_VGrp1EIE r v)

def _set_ICH_HCR_Type_VGrp1EIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_VGrp1EIE r v)

def _set_ICH_HCR_EL2_Type_vSGIEOICount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_vSGIEOICount r v)

def _set_ICH_HCR_Type_vSGIEOICount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_HCR_Type_vSGIEOICount r v)

def _set_ID_AA64MMFR0_EL1_Type_ASIDBits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_ASIDBits r v)

def _set_ID_AA64MMFR0_EL1_Type_BigEnd (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_BigEnd r v)

def _set_ID_AA64MMFR0_EL1_Type_BigEndEL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_BigEndEL0 r v)

def _set_ID_AA64MMFR0_EL1_Type_ExS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_ExS r v)

def _set_ID_AA64MMFR0_EL1_Type_FGT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_FGT r v)

def _set_ID_AA64MMFR0_EL1_Type_PARange (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_PARange r v)

def _set_ID_AA64MMFR0_EL1_Type_SNSMem (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_SNSMem r v)

def _set_ID_AA64MMFR0_EL1_Type_TGran16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran16 r v)

def _set_ID_AA64MMFR0_EL1_Type_TGran16_2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran16_2 r v)

def _set_ID_AA64MMFR0_EL1_Type_TGran4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran4 r v)

def _set_ID_AA64MMFR0_EL1_Type_TGran4_2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran4_2 r v)

def _set_ID_AA64MMFR0_EL1_Type_TGran64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran64 r v)

def _set_ID_AA64MMFR0_EL1_Type_TGran64_2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran64_2 r v)

def _set_HDFGRTR2_EL2_Type_nPMSSDATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMSSDATA r v)

def _set_HDFGRTR2_EL2_Type_nSPMDEVAFF_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMDEVAFF_EL1 r v)

def _set_HDFGRTR2_EL2_Type_nSPMID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMID r v)

def _set_VMPIDR_EL2_Type_Aff0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_Aff0 r v)

def _set_MPIDR_EL1_Type_Aff0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_EL1_Type_Aff0 r v)

def _set_MPIDR_Type_Aff0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MPIDR_Type_Aff0 r v)

def _set_VMPIDR_Type_Aff0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_VMPIDR_Type_Aff0 r v)

def _set_ID_AA64MMFR3_EL1_Type_ADERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_ADERR r v)

def _set_ID_AA64MMFR3_EL1_Type_ANERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_ANERR r v)

def _set_ID_AA64MMFR3_EL1_Type_D128_2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_D128_2 r v)

def _set_ID_AA64MMFR3_EL1_Type_MEC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_MEC r v)

def _set_ID_AA64MMFR3_EL1_Type_S1PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_S1PIE r v)

def _set_ID_AA64MMFR3_EL1_Type_S1POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_S1POE r v)

def _set_ID_AA64MMFR3_EL1_Type_SCTLRX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_SCTLRX r v)

def _set_ID_AA64MMFR3_EL1_Type_SDERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_SDERR r v)

def _set_ID_AA64MMFR3_EL1_Type_SNERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_SNERR r v)

def _set_ID_AA64MMFR3_EL1_Type_Spec_FPACC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_Spec_FPACC r v)

def _set_ID_AA64MMFR3_EL1_Type_TCRX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_TCRX r v)

def _set_ICH_VTR_EL2_Type_ListRegs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_ListRegs r v)

def _set_GICH_VTR_Type_ListRegs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VTR_Type_ListRegs r v)

def _set_ICH_VTR_Type_ListRegs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_Type_ListRegs r v)

def _set_ICH_VTR_EL2_Type_PREbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_PREbits r v)

def _set_GICH_VTR_Type_PREbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_VTR_Type_PREbits r v)

def _set_ICH_VTR_Type_PREbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_Type_PREbits r v)

def _set_ICH_VTR_EL2_Type_TDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_TDS r v)

def _set_ICH_VTR_Type_TDS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_Type_TDS r v)

def _set_ICH_VTR_EL2_Type_nV4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_nV4 r v)

def _set_ICH_VTR_Type_nV4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ICH_VTR_Type_nV4 r v)

def _set_ID_PFR1_EL1_Type_GenTimer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_GenTimer r v)

def _set_ID_PFR1_Type_GenTimer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_Type_GenTimer r v)

def _set_ID_PFR1_EL1_Type_MProgMod (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_MProgMod r v)

def _set_ID_PFR1_Type_MProgMod (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_Type_MProgMod r v)

def _set_ID_PFR1_EL1_Type_ProgMod (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_ProgMod r v)

def _set_ID_PFR1_Type_ProgMod (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_Type_ProgMod r v)

def _set_ID_PFR1_EL1_Type_Sec_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_Sec_frac r v)

def _set_ID_PFR1_Type_Sec_frac (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_Type_Sec_frac r v)

def _set_ID_PFR1_EL1_Type_Security (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_Security r v)

def _set_ID_PFR1_Type_Security (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_Type_Security r v)

def _set_ID_PFR1_EL1_Type_Virt_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_Virt_frac r v)

def _set_ID_PFR1_Type_Virt_frac (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_Type_Virt_frac r v)

def _set_ID_PFR1_EL1_Type_Virtualization (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_Virtualization r v)

def _set_ID_PFR1_Type_Virtualization (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_PFR1_Type_Virtualization r v)

def __set_MDSELR_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MDSELR_EL1_Type := value_name
  writeReg MDSELR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSELR_EL1) 3 0 (BitVec.slice r 0 4))
  writeReg MDSELR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSELR_EL1) 63 6 (BitVec.slice r 6 58))
  if ((! (←((pure ((← readReg NUM_BREAKPOINTS) ≤b 16)) <&&> (do
         (pure ((← readReg NUM_WATCHPOINTS) ≤b 16)))))) : Bool)
  then writeReg MDSELR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSELR_EL1) 5 4 (_get_MDSELR_EL1_Type_BANK r))
  else (pure ())

def _set_RNDRRS_Type_RNDRRS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_RNDRRS_Type_RNDRRS r v)

def _set_LORN_EL1_Type_Num (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_LORN_EL1_Type_Num r v)

def _set_CCSIDR_EL1_Type_Associativity (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 21)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR_EL1_Type_Associativity r v)

def _set_CCSIDR_Type_Associativity (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 21)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR_Type_Associativity r v)

def _set_CCSIDR_EL1_Type_LineSize (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR_EL1_Type_LineSize r v)

def _set_CCSIDR_Type_LineSize (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CCSIDR_Type_LineSize r v)

def _set_HFGRTR_EL2_Type_AIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_AIDR_EL1 r v)

def _set_HFGRTR_EL2_Type_CCSIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_CCSIDR_EL1 r v)

def _set_HFGRTR_EL2_Type_CLIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_CLIDR_EL1 r v)

def _set_HFGRTR_EL2_Type_CTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_CTR_EL0 r v)

def _set_HFGRTR_EL2_Type_DCZID_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_DCZID_EL0 r v)

def _set_HFGRTR_EL2_Type_ERRIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERRIDR_EL1 r v)

def _set_HFGRTR_EL2_Type_ERXFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXFR_EL1 r v)

def _set_HFGRTR_EL2_Type_ERXPFGF_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXPFGF_EL1 r v)

def _set_HFGRTR_EL2_Type_ISR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ISR_EL1 r v)

def _set_HFGRTR_EL2_Type_LORID_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_LORID_EL1 r v)

def _set_HFGRTR_EL2_Type_MIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_MIDR_EL1 r v)

def _set_HFGRTR_EL2_Type_MPIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_MPIDR_EL1 r v)

def _set_HFGRTR_EL2_Type_REVIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_REVIDR_EL1 r v)

def _set_ID_DFR0_EL1_Type_CopDbg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_CopDbg r v)

def _set_ID_DFR0_Type_CopDbg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_Type_CopDbg r v)

def _set_ID_DFR0_EL1_Type_CopSDbg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_CopSDbg r v)

def _set_ID_DFR0_Type_CopSDbg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_Type_CopSDbg r v)

def _set_ID_DFR0_EL1_Type_CopTrc (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_CopTrc r v)

def _set_ID_DFR0_Type_CopTrc (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_Type_CopTrc r v)

def _set_ID_DFR0_EL1_Type_MMapDbg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_MMapDbg r v)

def _set_ID_DFR0_Type_MMapDbg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_Type_MMapDbg r v)

def _set_ID_DFR0_EL1_Type_MMapTrc (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_MMapTrc r v)

def _set_ID_DFR0_Type_MMapTrc (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_Type_MMapTrc r v)

def _set_ID_DFR0_EL1_Type_MProfDbg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_MProfDbg r v)

def _set_ID_DFR0_Type_MProfDbg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_Type_MProfDbg r v)

def _set_ID_DFR0_EL1_Type_PerfMon (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_PerfMon r v)

def _set_ID_DFR0_Type_PerfMon (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_DFR0_Type_PerfMon r v)

def _set_PMXEVCNTR_EL0_Type_PMEVCNTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMXEVCNTR_EL0_Type_PMEVCNTR r v)

def _set_MVFR2_EL1_Type_FPMisc (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR2_EL1_Type_FPMisc r v)

def _set_MVFR2_Type_FPMisc (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR2_Type_FPMisc r v)

def _set_MVFR2_EL1_Type_SIMDMisc (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR2_EL1_Type_SIMDMisc r v)

def _set_MVFR2_Type_SIMDMisc (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_MVFR2_Type_SIMDMisc r v)

def _set_DBGAUTHSTATUS_EL1_Type_NSID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_NSID r v)

def _set_CTIAUTHSTATUS_Type_NSID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIAUTHSTATUS_Type_NSID r v)

def _set_DBGAUTHSTATUS_Type_NSID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_Type_NSID r v)

def _set_PMAUTHSTATUS_Type_NSID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_NSID r v)

def _set_DBGAUTHSTATUS_EL1_Type_NSNID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_NSNID r v)

def _set_CTIAUTHSTATUS_Type_NSNID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIAUTHSTATUS_Type_NSNID r v)

def _set_DBGAUTHSTATUS_Type_NSNID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_Type_NSNID r v)

def _set_PMAUTHSTATUS_Type_NSNID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_NSNID r v)

def _set_DBGAUTHSTATUS_EL1_Type_RLID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_RLID r v)

def _set_PMAUTHSTATUS_Type_RLID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_RLID r v)

def _set_DBGAUTHSTATUS_EL1_Type_RLNID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_RLNID r v)

def _set_PMAUTHSTATUS_Type_RLNID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_RLNID r v)

def _set_DBGAUTHSTATUS_EL1_Type_RTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_RTID r v)

def _set_PMAUTHSTATUS_Type_RTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_RTID r v)

def _set_DBGAUTHSTATUS_EL1_Type_RTNID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_RTNID r v)

def _set_PMAUTHSTATUS_Type_RTNID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_RTNID r v)

def _set_DBGAUTHSTATUS_EL1_Type_SID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_SID r v)

def _set_DBGAUTHSTATUS_Type_SID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_Type_SID r v)

def _set_PMAUTHSTATUS_Type_SID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_SID r v)

def _set_DBGAUTHSTATUS_EL1_Type_SNID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_SNID r v)

def _set_DBGAUTHSTATUS_Type_SNID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGAUTHSTATUS_Type_SNID r v)

def _set_PMAUTHSTATUS_Type_SNID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_SNID r v)

def _set_ID_MMFR3_EL1_Type_BPMaint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_EL1_Type_BPMaint r v)

def _set_ID_MMFR3_Type_BPMaint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_Type_BPMaint r v)

def _set_ID_MMFR3_EL1_Type_CMaintSW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_EL1_Type_CMaintSW r v)

def _set_ID_MMFR3_Type_CMaintSW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_Type_CMaintSW r v)

def _set_ID_MMFR3_EL1_Type_CMaintVA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_EL1_Type_CMaintVA r v)

def _set_ID_MMFR3_Type_CMaintVA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_Type_CMaintVA r v)

def _set_ID_MMFR3_EL1_Type_CMemSz (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_EL1_Type_CMemSz r v)

def _set_ID_MMFR3_Type_CMemSz (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_Type_CMemSz r v)

def _set_ID_MMFR3_EL1_Type_CohWalk (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_EL1_Type_CohWalk r v)

def _set_ID_MMFR3_Type_CohWalk (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_Type_CohWalk r v)

def _set_ID_MMFR3_EL1_Type_MaintBcst (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_EL1_Type_MaintBcst r v)

def _set_ID_MMFR3_Type_MaintBcst (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_Type_MaintBcst r v)

def _set_ID_MMFR3_EL1_Type_Supersec (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_EL1_Type_Supersec r v)

def _set_ID_MMFR3_Type_Supersec (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_MMFR3_Type_Supersec r v)

def _set_HDFGWTR_EL2_Type_OSLAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_OSLAR_EL1 r v)

def _set_HDFGWTR_EL2_Type_PMCR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMCR_EL0 r v)

def _set_HDFGWTR_EL2_Type_PMSWINC_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSWINC_EL0 r v)

def _set_HDFGWTR_EL2_Type_TRCOSLAR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCOSLAR r v)

def _set_HDFGWTR_EL2_Type_TRFCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRFCR_EL1 r v)

def _set_PMCEID1_EL0_Type_ID0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID0 r v)

def _set_PMCEID0_EL0_Type_ID0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID0 r v)

def _set_PMCEID0_Type_ID0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID0 r v)

def _set_PMCEID1_Type_ID0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID0 r v)

def _set_PMCEID1_EL0_Type_ID1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID1 r v)

def _set_PMCEID0_EL0_Type_ID1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID1 r v)

def _set_PMCEID0_Type_ID1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID1 r v)

def _set_PMCEID1_Type_ID1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID1 r v)

def _set_PMCEID1_EL0_Type_ID10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID10 r v)

def _set_PMCEID0_EL0_Type_ID10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID10 r v)

def _set_PMCEID0_Type_ID10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID10 r v)

def _set_PMCEID1_Type_ID10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID10 r v)

def _set_PMCEID1_EL0_Type_ID11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID11 r v)

def _set_PMCEID0_EL0_Type_ID11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID11 r v)

def _set_PMCEID0_Type_ID11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID11 r v)

def _set_PMCEID1_Type_ID11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID11 r v)

def _set_PMCEID1_EL0_Type_ID12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID12 r v)

def _set_PMCEID0_EL0_Type_ID12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID12 r v)

def _set_PMCEID0_Type_ID12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID12 r v)

def _set_PMCEID1_Type_ID12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID12 r v)

def _set_PMCEID1_EL0_Type_ID13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID13 r v)

def _set_PMCEID0_EL0_Type_ID13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID13 r v)

def _set_PMCEID0_Type_ID13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID13 r v)

def _set_PMCEID1_Type_ID13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID13 r v)

def _set_PMCEID1_EL0_Type_ID14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID14 r v)

def _set_PMCEID0_EL0_Type_ID14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID14 r v)

def _set_PMCEID0_Type_ID14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID14 r v)

def _set_PMCEID1_Type_ID14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID14 r v)

def _set_PMCEID1_EL0_Type_ID15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID15 r v)

def _set_PMCEID0_EL0_Type_ID15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID15 r v)

def _set_PMCEID0_Type_ID15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID15 r v)

def _set_PMCEID1_Type_ID15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID15 r v)

def _set_PMCEID1_EL0_Type_ID16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID16 r v)

def _set_PMCEID0_EL0_Type_ID16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID16 r v)

def _set_PMCEID0_Type_ID16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID16 r v)

def _set_PMCEID1_Type_ID16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID16 r v)

def _set_PMCEID1_EL0_Type_ID17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID17 r v)

def _set_PMCEID0_EL0_Type_ID17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID17 r v)

def _set_PMCEID0_Type_ID17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID17 r v)

def _set_PMCEID1_Type_ID17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID17 r v)

def _set_PMCEID1_EL0_Type_ID18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID18 r v)

def _set_PMCEID0_EL0_Type_ID18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID18 r v)

def _set_PMCEID0_Type_ID18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID18 r v)

def _set_PMCEID1_Type_ID18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID18 r v)

def _set_PMCEID1_EL0_Type_ID19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID19 r v)

def _set_PMCEID0_EL0_Type_ID19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID19 r v)

def _set_PMCEID0_Type_ID19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID19 r v)

def _set_PMCEID1_Type_ID19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID19 r v)

def _set_PMCEID1_EL0_Type_ID2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID2 r v)

def _set_PMCEID0_EL0_Type_ID2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID2 r v)

def _set_PMCEID0_Type_ID2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID2 r v)

def _set_PMCEID1_Type_ID2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID2 r v)

def _set_PMCEID1_EL0_Type_ID20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID20 r v)

def _set_PMCEID0_EL0_Type_ID20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID20 r v)

def _set_PMCEID0_Type_ID20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID20 r v)

def _set_PMCEID1_Type_ID20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID20 r v)

def _set_PMCEID1_EL0_Type_ID21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID21 r v)

def _set_PMCEID0_EL0_Type_ID21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID21 r v)

def _set_PMCEID0_Type_ID21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID21 r v)

def _set_PMCEID1_Type_ID21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID21 r v)

def _set_PMCEID1_EL0_Type_ID22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID22 r v)

def _set_PMCEID0_EL0_Type_ID22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID22 r v)

def _set_PMCEID0_Type_ID22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID22 r v)

def _set_PMCEID1_Type_ID22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID22 r v)

def _set_PMCEID1_EL0_Type_ID23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID23 r v)

def _set_PMCEID0_EL0_Type_ID23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID23 r v)

def _set_PMCEID0_Type_ID23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID23 r v)

def _set_PMCEID1_Type_ID23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID23 r v)

def _set_PMCEID1_EL0_Type_ID24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID24 r v)

def _set_PMCEID0_EL0_Type_ID24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID24 r v)

def _set_PMCEID0_Type_ID24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID24 r v)

def _set_PMCEID1_Type_ID24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID24 r v)

def _set_PMCEID1_EL0_Type_ID25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID25 r v)

def _set_PMCEID0_EL0_Type_ID25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID25 r v)

def _set_PMCEID0_Type_ID25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID25 r v)

def _set_PMCEID1_Type_ID25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID25 r v)

def _set_PMCEID1_EL0_Type_ID26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID26 r v)

def _set_PMCEID0_EL0_Type_ID26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID26 r v)

def _set_PMCEID0_Type_ID26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID26 r v)

def _set_PMCEID1_Type_ID26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID26 r v)

def _set_PMCEID1_EL0_Type_ID27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID27 r v)

def _set_PMCEID0_EL0_Type_ID27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID27 r v)

def _set_PMCEID0_Type_ID27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID27 r v)

def _set_PMCEID1_Type_ID27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID27 r v)

def _set_PMCEID1_EL0_Type_ID28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID28 r v)

def _set_PMCEID0_EL0_Type_ID28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID28 r v)

def _set_PMCEID0_Type_ID28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID28 r v)

def _set_PMCEID1_Type_ID28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID28 r v)

def _set_PMCEID1_EL0_Type_ID29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID29 r v)

def _set_PMCEID0_EL0_Type_ID29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID29 r v)

def _set_PMCEID0_Type_ID29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID29 r v)

def _set_PMCEID1_Type_ID29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID29 r v)

def _set_PMCEID1_EL0_Type_ID3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID3 r v)

def _set_PMCEID0_EL0_Type_ID3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID3 r v)

def _set_PMCEID0_Type_ID3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID3 r v)

def _set_PMCEID1_Type_ID3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID3 r v)

def _set_PMCEID1_EL0_Type_ID30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID30 r v)

def _set_PMCEID0_EL0_Type_ID30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID30 r v)

def _set_PMCEID0_Type_ID30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID30 r v)

def _set_PMCEID1_Type_ID30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID30 r v)

def _set_PMCEID1_EL0_Type_ID31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID31 r v)

def _set_PMCEID0_EL0_Type_ID31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID31 r v)

def _set_PMCEID0_Type_ID31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID31 r v)

def _set_PMCEID1_Type_ID31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID31 r v)

def _set_PMCEID1_EL0_Type_ID4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID4 r v)

def _set_PMCEID0_EL0_Type_ID4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID4 r v)

def _set_PMCEID0_Type_ID4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID4 r v)

def _set_PMCEID1_Type_ID4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID4 r v)

def _set_PMCEID1_EL0_Type_ID5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID5 r v)

def _set_PMCEID0_EL0_Type_ID5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID5 r v)

def _set_PMCEID0_Type_ID5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID5 r v)

def _set_PMCEID1_Type_ID5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID5 r v)

def _set_PMCEID1_EL0_Type_ID6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID6 r v)

def _set_PMCEID0_EL0_Type_ID6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID6 r v)

def _set_PMCEID0_Type_ID6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID6 r v)

def _set_PMCEID1_Type_ID6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID6 r v)

def _set_PMCEID1_EL0_Type_ID7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID7 r v)

def _set_PMCEID0_EL0_Type_ID7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID7 r v)

def _set_PMCEID0_Type_ID7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID7 r v)

def _set_PMCEID1_Type_ID7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID7 r v)

def _set_PMCEID1_EL0_Type_ID8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID8 r v)

def _set_PMCEID0_EL0_Type_ID8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID8 r v)

def _set_PMCEID0_Type_ID8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID8 r v)

def _set_PMCEID1_Type_ID8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID8 r v)

def _set_PMCEID1_EL0_Type_ID9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_ID9 r v)

def _set_PMCEID0_EL0_Type_ID9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_ID9 r v)

def _set_PMCEID0_Type_ID9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_Type_ID9 r v)

def _set_PMCEID1_Type_ID9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_Type_ID9 r v)

def _set_PMCEID1_EL0_Type_IDhi0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi0 r v)

def _set_PMCEID0_EL0_Type_IDhi0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi0 r v)

def _set_PMCEID2_Type_IDhi0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi0 r v)

def _set_PMCEID3_Type_IDhi0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi0 r v)

def _set_PMCEID1_EL0_Type_IDhi1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi1 r v)

def _set_PMCEID0_EL0_Type_IDhi1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi1 r v)

def _set_PMCEID2_Type_IDhi1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi1 r v)

def _set_PMCEID3_Type_IDhi1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi1 r v)

def _set_PMCEID1_EL0_Type_IDhi10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi10 r v)

def _set_PMCEID0_EL0_Type_IDhi10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi10 r v)

def _set_PMCEID2_Type_IDhi10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi10 r v)

def _set_PMCEID3_Type_IDhi10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi10 r v)

def _set_PMCEID1_EL0_Type_IDhi11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi11 r v)

def _set_PMCEID0_EL0_Type_IDhi11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi11 r v)

def _set_PMCEID2_Type_IDhi11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi11 r v)

def _set_PMCEID3_Type_IDhi11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi11 r v)

def _set_PMCEID1_EL0_Type_IDhi12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi12 r v)

def _set_PMCEID0_EL0_Type_IDhi12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi12 r v)

def _set_PMCEID2_Type_IDhi12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi12 r v)

def _set_PMCEID3_Type_IDhi12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi12 r v)

def _set_PMCEID1_EL0_Type_IDhi13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi13 r v)

def _set_PMCEID0_EL0_Type_IDhi13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi13 r v)

def _set_PMCEID2_Type_IDhi13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi13 r v)

def _set_PMCEID3_Type_IDhi13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi13 r v)

def _set_PMCEID1_EL0_Type_IDhi14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi14 r v)

def _set_PMCEID0_EL0_Type_IDhi14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi14 r v)

def _set_PMCEID2_Type_IDhi14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi14 r v)

def _set_PMCEID3_Type_IDhi14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi14 r v)

def _set_PMCEID1_EL0_Type_IDhi15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi15 r v)

def _set_PMCEID0_EL0_Type_IDhi15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi15 r v)

def _set_PMCEID2_Type_IDhi15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi15 r v)

def _set_PMCEID3_Type_IDhi15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi15 r v)

def _set_PMCEID1_EL0_Type_IDhi16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi16 r v)

def _set_PMCEID0_EL0_Type_IDhi16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi16 r v)

def _set_PMCEID2_Type_IDhi16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi16 r v)

def _set_PMCEID3_Type_IDhi16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi16 r v)

def _set_PMCEID1_EL0_Type_IDhi17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi17 r v)

def _set_PMCEID0_EL0_Type_IDhi17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi17 r v)

def _set_PMCEID2_Type_IDhi17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi17 r v)

def _set_PMCEID3_Type_IDhi17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi17 r v)

def _set_PMCEID1_EL0_Type_IDhi18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi18 r v)

def _set_PMCEID0_EL0_Type_IDhi18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi18 r v)

def _set_PMCEID2_Type_IDhi18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi18 r v)

def _set_PMCEID3_Type_IDhi18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi18 r v)

def _set_PMCEID1_EL0_Type_IDhi19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi19 r v)

def _set_PMCEID0_EL0_Type_IDhi19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi19 r v)

def _set_PMCEID2_Type_IDhi19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi19 r v)

def _set_PMCEID3_Type_IDhi19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi19 r v)

def _set_PMCEID1_EL0_Type_IDhi2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi2 r v)

def _set_PMCEID0_EL0_Type_IDhi2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi2 r v)

def _set_PMCEID2_Type_IDhi2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi2 r v)

def _set_PMCEID3_Type_IDhi2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi2 r v)

def _set_PMCEID1_EL0_Type_IDhi20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi20 r v)

def _set_PMCEID0_EL0_Type_IDhi20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi20 r v)

def _set_PMCEID2_Type_IDhi20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi20 r v)

def _set_PMCEID3_Type_IDhi20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi20 r v)

def _set_PMCEID1_EL0_Type_IDhi21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi21 r v)

def _set_PMCEID0_EL0_Type_IDhi21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi21 r v)

def _set_PMCEID2_Type_IDhi21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi21 r v)

def _set_PMCEID3_Type_IDhi21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi21 r v)

def _set_PMCEID1_EL0_Type_IDhi22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi22 r v)

def _set_PMCEID0_EL0_Type_IDhi22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi22 r v)

def _set_PMCEID2_Type_IDhi22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi22 r v)

def _set_PMCEID3_Type_IDhi22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi22 r v)

def _set_PMCEID1_EL0_Type_IDhi23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi23 r v)

def _set_PMCEID0_EL0_Type_IDhi23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi23 r v)

def _set_PMCEID2_Type_IDhi23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi23 r v)

def _set_PMCEID3_Type_IDhi23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi23 r v)

def _set_PMCEID1_EL0_Type_IDhi24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi24 r v)

def _set_PMCEID0_EL0_Type_IDhi24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi24 r v)

def _set_PMCEID2_Type_IDhi24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi24 r v)

def _set_PMCEID3_Type_IDhi24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi24 r v)

def _set_PMCEID1_EL0_Type_IDhi25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi25 r v)

def _set_PMCEID0_EL0_Type_IDhi25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi25 r v)

def _set_PMCEID2_Type_IDhi25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi25 r v)

def _set_PMCEID3_Type_IDhi25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi25 r v)

def _set_PMCEID1_EL0_Type_IDhi26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi26 r v)

def _set_PMCEID0_EL0_Type_IDhi26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi26 r v)

def _set_PMCEID2_Type_IDhi26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi26 r v)

def _set_PMCEID3_Type_IDhi26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi26 r v)

def _set_PMCEID1_EL0_Type_IDhi27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi27 r v)

def _set_PMCEID0_EL0_Type_IDhi27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi27 r v)

def _set_PMCEID2_Type_IDhi27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi27 r v)

def _set_PMCEID3_Type_IDhi27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi27 r v)

def _set_PMCEID1_EL0_Type_IDhi28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi28 r v)

def _set_PMCEID0_EL0_Type_IDhi28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi28 r v)

def _set_PMCEID2_Type_IDhi28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi28 r v)

def _set_PMCEID3_Type_IDhi28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi28 r v)

def _set_PMCEID1_EL0_Type_IDhi29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi29 r v)

def _set_PMCEID0_EL0_Type_IDhi29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi29 r v)

def _set_PMCEID2_Type_IDhi29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi29 r v)

def _set_PMCEID3_Type_IDhi29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi29 r v)

def _set_PMCEID1_EL0_Type_IDhi3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi3 r v)

def _set_PMCEID0_EL0_Type_IDhi3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi3 r v)

def _set_PMCEID2_Type_IDhi3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi3 r v)

def _set_PMCEID3_Type_IDhi3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi3 r v)

def _set_PMCEID1_EL0_Type_IDhi30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi30 r v)

def _set_PMCEID0_EL0_Type_IDhi30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi30 r v)

def _set_PMCEID2_Type_IDhi30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi30 r v)

def _set_PMCEID3_Type_IDhi30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi30 r v)

def _set_PMCEID1_EL0_Type_IDhi31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi31 r v)

def _set_PMCEID0_EL0_Type_IDhi31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi31 r v)

def _set_PMCEID2_Type_IDhi31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi31 r v)

def _set_PMCEID3_Type_IDhi31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi31 r v)

def _set_PMCEID1_EL0_Type_IDhi4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi4 r v)

def _set_PMCEID0_EL0_Type_IDhi4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi4 r v)

def _set_PMCEID2_Type_IDhi4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi4 r v)

def _set_PMCEID3_Type_IDhi4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi4 r v)

def _set_PMCEID1_EL0_Type_IDhi5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi5 r v)

def _set_PMCEID0_EL0_Type_IDhi5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi5 r v)

def _set_PMCEID2_Type_IDhi5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi5 r v)

def _set_PMCEID3_Type_IDhi5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi5 r v)

def _set_PMCEID1_EL0_Type_IDhi6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi6 r v)

def _set_PMCEID0_EL0_Type_IDhi6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi6 r v)

def _set_PMCEID2_Type_IDhi6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi6 r v)

def _set_PMCEID3_Type_IDhi6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi6 r v)

def _set_PMCEID1_EL0_Type_IDhi7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi7 r v)

def _set_PMCEID0_EL0_Type_IDhi7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi7 r v)

def _set_PMCEID2_Type_IDhi7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi7 r v)

def _set_PMCEID3_Type_IDhi7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi7 r v)

def _set_PMCEID1_EL0_Type_IDhi8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi8 r v)

def _set_PMCEID0_EL0_Type_IDhi8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi8 r v)

def _set_PMCEID2_Type_IDhi8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi8 r v)

def _set_PMCEID3_Type_IDhi8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi8 r v)

def _set_PMCEID1_EL0_Type_IDhi9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID1_EL0_Type_IDhi9 r v)

def _set_PMCEID0_EL0_Type_IDhi9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID0_EL0_Type_IDhi9 r v)

def _set_PMCEID2_Type_IDhi9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID2_Type_IDhi9 r v)

def _set_PMCEID3_Type_IDhi9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCEID3_Type_IDhi9 r v)

def __get_selected_SPMACCESSR_EL3_field (_ : Unit) : SailM (BitVec 2) := do
  let idx ← do (pure ((BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL (← readReg SPMSELR_EL0))) *i 2))
  (pure (BitVec.slice (← readReg SPMACCESSR_EL3) idx 2))

def _set_ID_AA64ZFR0_EL1_Type_B16B16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_B16B16 r v)

def _set_ID_AA64SMFR0_EL1_Type_B16B16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_B16B16 r v)

def _set_ID_AA64ZFR0_EL1_Type_BitPerm (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_BitPerm r v)

def _set_ID_AA64ZFR0_EL1_Type_F32MM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_F32MM r v)

def _set_ID_AA64ZFR0_EL1_Type_F64MM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_F64MM r v)

def _set_ID_AA64ZFR0_EL1_Type_SVEver (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_SVEver r v)

def CNTP_CVAL_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTP_CVAL_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg CNTP_CVAL_S r
  else (CNTP_CVAL_NS_write r)

def _set_ID_AA64SMFR0_EL1_Type_B16F32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_B16F32 r v)

def _set_ID_AA64SMFR0_EL1_Type_BI32I32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_BI32I32 r v)

def _set_ID_AA64SMFR0_EL1_Type_F16F16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_F16F16 r v)

def _set_ID_AA64SMFR0_EL1_Type_F16F32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_F16F32 r v)

def _set_ID_AA64SMFR0_EL1_Type_F32F32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_F32F32 r v)

def _set_ID_AA64SMFR0_EL1_Type_F64F64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_F64F64 r v)

def _set_ID_AA64SMFR0_EL1_Type_I16I32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_I16I32 r v)

def _set_ID_AA64SMFR0_EL1_Type_I16I64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_I16I64 r v)

def _set_ID_AA64SMFR0_EL1_Type_I8I32 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_I8I32 r v)

def _set_ID_AA64SMFR0_EL1_Type_SMEver (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_SMEver r v)

def __set_MPAM3_EL3 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM3_EL3_Type := value_name
  (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 63 (← (MPAM3_EL3_read ())) 0 (BitVec.slice r 0 63))))
  (MPAM3_EL3_write (_update_MPAM3_EL3_Type_MPAMEN (← (MPAM3_EL3_read ())) (_get_MPAM3_EL3_Type_MPAMEN r)))

def _set_AMEVCNTR1_EL0_Type_ACNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVCNTR1_EL0_Type_ACNT r v)

def _set_AMEVCNTR0_EL0_Type_ACNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVCNTR0_EL0_Type_ACNT r v)

def _set_AMEVCNTR0_Type_ACNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVCNTR0_Type_ACNT r v)

def _set_AMEVCNTR1_Type_ACNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMEVCNTR1_Type_ACNT r v)

def _set_AMCR_EL0_Type_CG1RZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCR_EL0_Type_CG1RZ r v)

def _set_AMCR_Type_CG1RZ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCR_Type_CG1RZ r v)

def _set_AMCFGR_EL0_Type_NCG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCFGR_EL0_Type_NCG r v)

def _set_AMCFGR_Type_NCG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCFGR_Type_NCG r v)

def _set_PMCFGR_Type_NCG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_NCG r v)

def _set_AMCFGR_EL0_Type_SIZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCFGR_EL0_Type_SIZE r v)

def _set_AMCFGR_Type_SIZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCFGR_Type_SIZE r v)

def _set_AMPIDR4_Type_SIZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR4_Type_SIZE r v)

def _set_CTIPIDR4_Type_SIZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR4_Type_SIZE r v)

def _set_EDPIDR4_Type_SIZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR4_Type_SIZE r v)

def _set_PMCFGR_Type_SIZE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_SIZE r v)

def _set_PMPIDR4_Type_SIZE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR4_Type_SIZE r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF10_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF10_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF110_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF110_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF111_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF111_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF112_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF112_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF113_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF113_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF114_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF114_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF115_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF115_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF11_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF11_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF12_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF12_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF13_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF13_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF14_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF14_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF15_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF15_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF16_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF16_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF17_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF17_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF18_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF18_EL2 r v)

def _set_AMCG1IDR_EL0_Type_AMEVCNTOFF19_EL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTOFF19_EL2 r v)

def _set_AMCGCR_EL0_Type_CG0NC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCGCR_EL0_Type_CG0NC r v)

def _set_AMCGCR_Type_CG0NC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCGCR_Type_CG0NC r v)

def _set_PMCGCR0_Type_CG0NC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCGCR0_Type_CG0NC r v)

def _set_AMCGCR_EL0_Type_CG1NC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCGCR_EL0_Type_CG1NC r v)

def _set_AMCGCR_Type_CG1NC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCGCR_Type_CG1NC r v)

def _set_PMCGCR0_Type_CG1NC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCGCR0_Type_CG1NC r v)

def __set_PMSNEVFR_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMSNEVFR_EL1_Type := value_name
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 63 is not implemented, or filtering on event 63 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 63 63 (_get_PMSNEVFR_EL1_Type_E63 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 62 is not implemented, or filtering on event 62 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 62 62 (_get_PMSNEVFR_EL1_Type_E62 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 61 is not implemented, or filtering on event 61 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 61 61 (_get_PMSNEVFR_EL1_Type_E61 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 60 is not implemented, or filtering on event 60 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 60 60 (_get_PMSNEVFR_EL1_Type_E60 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 59 is not implemented, or filtering on event 59 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 59 59 (_get_PMSNEVFR_EL1_Type_E59 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 58 is not implemented, or filtering on event 58 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 58 58 (_get_PMSNEVFR_EL1_Type_E58 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 57 is not implemented, or filtering on event 57 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 57 57 (_get_PMSNEVFR_EL1_Type_E57 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 56 is not implemented, or filtering on event 56 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 56 56 (_get_PMSNEVFR_EL1_Type_E56 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 55 is not implemented, or filtering on event 55 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 55 55 (_get_PMSNEVFR_EL1_Type_E55 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 54 is not implemented, or filtering on event 54 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 54 54 (_get_PMSNEVFR_EL1_Type_E54 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 53 is not implemented, or filtering on event 53 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 53 53 (_get_PMSNEVFR_EL1_Type_E53 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 52 is not implemented, or filtering on event 52 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 52 52 (_get_PMSNEVFR_EL1_Type_E52 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 51 is not implemented, or filtering on event 51 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 51 51 (_get_PMSNEVFR_EL1_Type_E51 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 50 is not implemented, or filtering on event 50 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 50 50 (_get_PMSNEVFR_EL1_Type_E50 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 49 is not implemented, or filtering on event 49 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 49 49 (_get_PMSNEVFR_EL1_Type_E49 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 48 is not implemented, or filtering on event 48 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 48 48 (_get_PMSNEVFR_EL1_Type_E48 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 31 is not implemented, or filtering on event 31 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 31 31 (_get_PMSNEVFR_EL1_Type_E31 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 30 is not implemented, or filtering on event 30 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 30 30 (_get_PMSNEVFR_EL1_Type_E30 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 29 is not implemented, or filtering on event 29 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 29 29 (_get_PMSNEVFR_EL1_Type_E29 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 28 is not implemented, or filtering on event 28 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 28 28 (_get_PMSNEVFR_EL1_Type_E28 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 27 is not implemented, or filtering on event 27 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 27 27 (_get_PMSNEVFR_EL1_Type_E27 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 26 is not implemented, or filtering on event 26 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 26 26 (_get_PMSNEVFR_EL1_Type_E26 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 25 is not implemented, or filtering on event 25 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 25 25 (_get_PMSNEVFR_EL1_Type_E25 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 24 is not implemented, or filtering on event 24 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 24 24 (_get_PMSNEVFR_EL1_Type_E24 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 15 is not implemented, or filtering on event 15 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 15 15 (_get_PMSNEVFR_EL1_Type_E15 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 14 is not implemented, or filtering on event 14 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 14 14 (_get_PMSNEVFR_EL1_Type_E14 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 13 is not implemented, or filtering on event 13 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 13 13 (_get_PMSNEVFR_EL1_Type_E13 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  let r ← (( do
    if ((! (← (__IMPDEF_boolean "event 12 is not implemented, or filtering on event 12 is not supported"))) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 12 12 (_get_PMSNEVFR_EL1_Type_E12 (← readReg PMSNEVFR_EL1)))))
    else (pure r) ) : SailM (BitVec 64) )
  writeReg PMSNEVFR_EL1 r

def _set_ERRIDR_EL1_Type_NUM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRIDR_EL1_Type_NUM r v)

def _set_ERRIDR_Type_NUM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_ERRIDR_Type_NUM r v)

def __set_BRBSRCINJ_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : BRBSRCINJ_EL1_Type := value_name
  if ((! (←((pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b00#2)) <||> (do
         (pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b01#2)))))) : Bool)
  then writeReg BRBSRCINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBSRCINJ_EL1) 63 0 (_get_BRBSRCINJ_EL1_Type_ADDRESS r))
  else (pure ())

def __set_BRBINFINJ_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : BRBINFINJ_EL1_Type := value_name
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 4 0 (BitVec.slice r 0 5))
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 15 14 (BitVec.slice r 14 2))
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 31 18 (BitVec.slice r 18 14))
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 63 47 (BitVec.slice r 47 17))
  if ((! ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b00#2)) : Bool)
  then writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 46 46 (_get_BRBINFINJ_EL1_Type_CCU r))
  else (pure ())
  if ((! (←((pure ((_get_BRBINFINJ_EL1_Type_CCU (← readReg BRBINFINJ_EL1)) == 1#1)) <||> (do
         (pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b00#2)))))) : Bool)
  then writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 45 32 (_get_BRBINFINJ_EL1_Type_CC r))
  else (pure ())
  if ((! ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b00#2)) : Bool)
  then writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 17 17 (_get_BRBINFINJ_EL1_Type_LASTFAILED r))
  else (pure ())
  if ((! (←((pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b00#2)) <||> (do
         (pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b01#2)))))) : Bool)
  then writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 16 16 (_get_BRBINFINJ_EL1_Type_T r))
  else (pure ())
  if ((! ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b00#2)) : Bool)
  then writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 13 8 (_get_BRBINFINJ_EL1_Type_TYPE r))
  else (pure ())
  if ((! (←((pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b00#2)) <||> (do
         (pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b10#2)))))) : Bool)
  then writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 7 6 (_get_BRBINFINJ_EL1_Type_EL r))
  else (pure ())
  if ((! (←((pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b00#2)) <||> (do
         (pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b01#2))) <||> (do
         (pure ((BitVec.join1 [(BitVec.access (_get_BRBINFINJ_EL1_Type_TYPE (← readReg BRBINFINJ_EL1)) 5)]) == 1#1)))))) : Bool)
  then writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBINFINJ_EL1) 5 5 (_get_BRBINFINJ_EL1_Type_MPRED r))
  else (pure ())

def __set_BRBTGTINJ_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : BRBTGTINJ_EL1_Type := value_name
  if ((! (←((pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b00#2)) <||> (do
         (pure ((_get_BRBINFINJ_EL1_Type_VALID (← readReg BRBINFINJ_EL1)) == 0b10#2)))))) : Bool)
  then writeReg BRBTGTINJ_EL1 (Sail.BitVec.updateSubrange (← readReg BRBTGTINJ_EL1) 63 0 (_get_BRBTGTINJ_EL1_Type_ADDRESS r))
  else (pure ())

def _set_GITS_CREADR_Type_Offset (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 15)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CREADR_Type_Offset r v)

def _set_GITS_CWRITER_Type_Offset (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 15)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CWRITER_Type_Offset r v)

def _set_GITS_CREADR_Type_Stalled (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CREADR_Type_Stalled r v)

def _set_GICR_PENDBASER_Type_InnerCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_InnerCache r v)

def _set_GICR_PROPBASER_Type_InnerCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PROPBASER_Type_InnerCache r v)

def _set_GICR_VPENDBASER_Type_InnerCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_InnerCache r v)

def _set_GICR_VPROPBASER_Type_InnerCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_InnerCache r v)

def _set_GITS_CBASER_Type_InnerCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CBASER_Type_InnerCache r v)

def _set_GICR_PENDBASER_Type_OuterCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_OuterCache r v)

def _set_GICR_PROPBASER_Type_OuterCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PROPBASER_Type_OuterCache r v)

def _set_GICR_VPENDBASER_Type_OuterCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_OuterCache r v)

def _set_GICR_VPROPBASER_Type_OuterCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_OuterCache r v)

def _set_GITS_CBASER_Type_OuterCache (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CBASER_Type_OuterCache r v)

def _set_GICR_PENDBASER_Type_PTZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_PTZ r v)

def _set_GICR_PENDBASER_Type_Physical_Address (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 36)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_Physical_Address r v)

def _set_GICR_PROPBASER_Type_Physical_Address (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 40)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PROPBASER_Type_Physical_Address r v)

def _set_GICR_VPENDBASER_Type_Physical_Address (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 36)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_Physical_Address r v)

def _set_GICR_VPROPBASER_Type_Physical_Address (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 40)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Physical_Address r v)

def _set_GITS_CBASER_Type_Physical_Address (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 40)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CBASER_Type_Physical_Address r v)

def _set_GICR_PENDBASER_Type_Shareability (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PENDBASER_Type_Shareability r v)

def _set_GICR_PROPBASER_Type_Shareability (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PROPBASER_Type_Shareability r v)

def _set_GICR_VPENDBASER_Type_Shareability (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_Shareability r v)

def _set_GICR_VPROPBASER_Type_Shareability (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Shareability r v)

def _set_GITS_CBASER_Type_Shareability (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CBASER_Type_Shareability r v)

def _set_GICR_VPROPBASER_Type_Entry_Size (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Entry_Size r v)

def _set_GICR_VPROPBASER_Type_Indirect (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Indirect r v)

def _set_GICR_VPROPBASER_Type_Page_Size (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Page_Size r v)

def _set_GICR_VPROPBASER_Type_Size (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 7)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Size r v)

def _set_GITS_CBASER_Type_Size (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CBASER_Type_Size r v)

def _set_GICR_INVALLR_Type_vPEID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INVALLR_Type_vPEID r v)

def _set_GICR_INVLPIR_Type_vPEID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INVLPIR_Type_vPEID r v)

def _set_GICR_VPENDBASER_Type_vPEID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_vPEID r v)

def _set_GICR_VSGIR_Type_vPEID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VSGIR_Type_vPEID r v)

def _set_GITS_SGIR_Type_vPEID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_SGIR_Type_vPEID r v)

def _set_EDHSR_Type_FnP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDHSR_Type_FnP r v)

def _set_EDHSR_Type_VNCR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDHSR_Type_VNCR r v)

def _set_EDHSR_Type_WPF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDHSR_Type_WPF r v)

def _set_EDHSR_Type_WPT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDHSR_Type_WPT r v)

def _set_EDHSR_Type_WPTV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDHSR_Type_WPTV r v)

def _set_GICR_VPENDBASER_Type_Dirty (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_Dirty r v)

def _set_GICR_VPENDBASER_Type_Doorbell (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_Doorbell r v)

def _set_GICR_VPENDBASER_Type_IDAI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_IDAI r v)

def _set_GICR_VPENDBASER_Type_PendingLast (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_PendingLast r v)

def _set_GICR_VPENDBASER_Type_VGrp0En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_VGrp0En r v)

def _set_GICR_VPENDBASER_Type_VGrp1En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_VGrp1En r v)

def _set_GITS_TYPER_Type_CCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_CCT r v)

def _set_GITS_TYPER_Type_CIDbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_CIDbits r v)

def _set_GITS_TYPER_Type_CIL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_CIL r v)

def _set_GITS_TYPER_Type_Devbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_Devbits r v)

def _set_GITS_TYPER_Type_HCC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_HCC r v)

def _set_GITS_TYPER_Type_ID_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_ID_bits r v)

def _set_GITS_TYPER_Type_INV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_INV r v)

def _set_GITS_TYPER_Type_ITT_entry_size (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_ITT_entry_size r v)

def _set_GITS_TYPER_Type_PTA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_PTA r v)

def _set_GITS_TYPER_Type_Physical (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_Physical r v)

def _set_GITS_TYPER_Type_SVPET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_SVPET r v)

def _set_GITS_TYPER_Type_UMSI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_UMSI r v)

def _set_GITS_STATUSR_Type_UMSI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_STATUSR_Type_UMSI r v)

def _set_GITS_TYPER_Type_UMSIirq (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_UMSIirq r v)

def _set_GITS_CTLR_Type_UMSIirq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CTLR_Type_UMSIirq r v)

def _set_GITS_TYPER_Type_VMAPP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_VMAPP r v)

def _set_GITS_TYPER_Type_VMOVP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_VMOVP r v)

def _set_GITS_TYPER_Type_VSGI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_VSGI r v)

def _set_GITS_TYPER_Type_Virtual (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_Virtual r v)

def _set_GITS_TYPER_Type_nID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_TYPER_Type_nID r v)

def _set_GITS_CWRITER_Type_Retry (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CWRITER_Type_Retry r v)

def _set_EDAA32PFR_Type_MSA_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDAA32PFR_Type_MSA_frac r v)

def _set_PMCFGR_Type_CCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_CCD r v)

def _set_PMCFGR_Type_NA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCFGR_Type_NA r v)

def _set_PMIIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMIIDR_Type_ProductID r v)

def _set_AMIIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMIIDR_Type_ProductID r v)

def _set_GICD_IIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_IIDR_Type_ProductID r v)

def _set_GICM_IIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_IIDR_Type_ProductID r v)

def _set_GICR_IIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_IIDR_Type_ProductID r v)

def _set_GITS_IIDR_Type_ProductID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_IIDR_Type_ProductID r v)

def AIFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM AIFSR_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg AIFSR_S)
  else (do (AIFSR_NS_read ()))

def AIFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AIFSR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg AIFSR_S r
  else (AIFSR_NS_write r)

def __set_HCPTR (value_name : (BitVec 32)) : SailM Unit := do
  let r : HCPTR_Type := value_name
  (HCPTR_write (Mk_HCPTR_Type (set_slice 10 (← (HCPTR_read ())) 0 (BitVec.slice r 0 10))))
  (HCPTR_write (Mk_HCPTR_Type (set_slice 20 (← (HCPTR_read ())) 12 (BitVec.slice r 12 20))))
  if ((! (←((pure (HaveEL EL3)) <&&> (do
         (ELUsingAArch32 EL3)) <&&> (do
         (pure (! (← (IsCurrentSecurityState SS_Secure))))) <&&> (do
         (pure ((_get_NSACR_Type_cp10 (← readReg NSACR)) == 0#1)))))) : Bool)
  then (HCPTR_write (_update_HCPTR_Type_TCP11 (← (HCPTR_read ())) (_get_HCPTR_Type_TCP11 r)))
  else (pure ())
  if ((! (←((pure (HaveEL EL3)) <&&> (do
         (ELUsingAArch32 EL3)) <&&> (do
         (pure (! (← (IsCurrentSecurityState SS_Secure))))) <&&> (do
         (pure ((_get_NSACR_Type_cp10 (← readReg NSACR)) == 0#1)))))) : Bool)
  then (HCPTR_write (_update_HCPTR_Type_TCP10 (← (HCPTR_read ())) (_get_HCPTR_Type_TCP10 r)))
  else (pure ())

def DACR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DACR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg DACR_S r
  else (DACR_NS_write r)

def __set_PMCR (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCR_Type := value_name
  (PMCR_write (Mk_PMCR_Type (set_slice 1 (← (PMCR_read ())) 0 (BitVec.slice r 0 1))))
  (PMCR_write (Mk_PMCR_Type (set_slice 13 (← (PMCR_read ())) 3 (BitVec.slice r 3 13))))
  if ((! (! (← (IsFeatureImplemented FEAT_PMUv3p7)))) : Bool)
  then (PMCR_write (_update_PMCR_Type_IMP (← (PMCR_read ())) (_get_PMCR_Type_IMP r)))
  else (pure ())
  if ((! ((_get_PMCR_Type_IMP (← (PMCR_read ()))) != 0b00000000#8)) : Bool)
  then (PMCR_write (_update_PMCR_Type_IDCODE (← (PMCR_read ())) (_get_PMCR_Type_IDCODE r)))
  else (pure ())
  (PMCR_write (_update_PMCR_Type_C (← (PMCR_read ())) (_get_PMCR_Type_C r)))
  (PMCR_write (_update_PMCR_Type_P (← (PMCR_read ())) (_get_PMCR_Type_P r)))

def _set_DBGDEVID1_Type_PCSROffset (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID1_Type_PCSROffset r v)

def _set_EDDEVID1_Type_PCSROffset (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVID1_Type_PCSROffset r v)

def TPIDRURW_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM TPIDRURW_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg TPIDRURW_S)
  else (do (TPIDRURW_NS_read ()))

def TPIDRURW_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRURW_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg TPIDRURW_S r
  else (TPIDRURW_NS_write r)

def ADFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM ADFSR_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg ADFSR_S)
  else (do (ADFSR_NS_read ()))

def ADFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ADFSR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg ADFSR_S r
  else (ADFSR_NS_write r)

def _set_CNTHCTL_Type_PL1PCEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_Type_PL1PCEN r v)

def _set_CNTHCTL_Type_PL1PCTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHCTL_Type_PL1PCTEN r v)

def _set_FPSID_Type_Subarchitecture (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 7)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_FPSID_Type_Subarchitecture r v)

def TPIDRURO_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM TPIDRURO_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg TPIDRURO_S)
  else (do (TPIDRURO_NS_read ()))

def TPIDRURO_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRURO_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg TPIDRURO_S r
  else (TPIDRURO_NS_write r)

def __get_selected_PMEVCNTR (_ : Unit) : SailM (BitVec 32) := do
  let idx ← do (pure (BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))))
  sail_assert (idx ≤b 30) "src/v8_base.sail:49451.20-49451.21"
  (PMEVCNTR_read idx)

def __set_selected_PMEVCNTR (value_name : (BitVec 32)) : SailM Unit := do
  let idx ← do (pure (BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))))
  sail_assert (idx ≤b 30) "src/v8_base.sail:49459.20-49459.21"
  (PMEVCNTR_set idx value_name)

def _set_DBGDTRTXext_Type_DTRTX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTRTXext_Type_DTRTX r v)

def _set_DBGDTRTXint_Type_DTRTX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTRTXint_Type_DTRTX r v)

def ACTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM ACTLR_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg ACTLR_S)
  else (do (ACTLR_NS_read ()))

def ACTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ACTLR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg ACTLR_S r
  else (ACTLR_NS_write r)

def _set_DBGOSLAR_Type_OSLA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGOSLAR_Type_OSLA r v)

def _set_DBGDTRRXext_Type_DTRRX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTRRXext_Type_DTRRX r v)

def _set_DBGDTRRXint_Type_DTRRX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDTRRXint_Type_DTRRX r v)

/-- Type quantifiers: n : Int -/
def ICC_AP1R_read (n : Int) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM ICC_AP1R_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then
    (do
      sail_assert ((0 ≤b n) && (n <b 4)) "src/v8_base.sail:49731.45-49731.46"
      (ICC_AP1R_S_read n))
  else
    (do
      sail_assert ((0 ≤b n) && (n <b 4)) "src/v8_base.sail:49734.45-49734.46"
      (ICC_AP1R_NS_read n))

/-- Type quantifiers: n : Int -/
def ICC_AP1R_set (n : Int) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_AP1R_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then
    (do
      sail_assert ((0 ≤b n) && (n <b 4)) "src/v8_base.sail:49745.45-49745.46"
      (ICC_AP1R_S_set n r))
  else
    (do
      sail_assert ((0 ≤b n) && (n <b 4)) "src/v8_base.sail:49748.45-49748.46"
      (ICC_AP1R_NS_set n r))

def AMAIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM AMAIR0_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg AMAIR0_S)
  else (do (AMAIR0_NS_read ()))

def AMAIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMAIR0_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg AMAIR0_S r
  else (AMAIR0_NS_write r)

def __set_HSCTLR (value_name : (BitVec 32)) : SailM Unit := do
  let r : HSCTLR_Type := value_name
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 5 (← (HSCTLR_read ())) 0 (BitVec.slice r 0 5))))
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 1 (← (HSCTLR_read ())) 6 (BitVec.slice r 6 1))))
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 24 (← (HSCTLR_read ())) 8 (BitVec.slice r 8 24))))
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_ITD")))) : Bool)
  then (HSCTLR_write (_update_HSCTLR_Type_ITD (← (HSCTLR_read ())) (_get_HSCTLR_Type_ITD r)))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_CP15BEN")))) : Bool)
  then (HSCTLR_write (_update_HSCTLR_Type_CP15BEN (← (HSCTLR_read ())) (_get_HSCTLR_Type_CP15BEN r)))
  else (pure ())

def _set_TLBTR_Type_nU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_TLBTR_Type_nU r v)

def _set_DBGDEVID_Type_AuxRegs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID_Type_AuxRegs r v)

def _set_EDDEVID_Type_AuxRegs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVID_Type_AuxRegs r v)

def _set_DBGDEVID_Type_BPAddrMask (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID_Type_BPAddrMask r v)

def _set_DBGDEVID_Type_CIDMask (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID_Type_CIDMask r v)

def _set_DBGDEVID_Type_VectorCatch (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID_Type_VectorCatch r v)

def _set_DBGDEVID_Type_VirtExtns (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID_Type_VirtExtns r v)

def _set_DBGDEVID_Type_WPAddrMask (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDEVID_Type_WPAddrMask r v)

def ACTLR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM ACTLR2_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg ACTLR2_S)
  else (do (ACTLR2_NS_read ()))

def ACTLR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ACTLR2_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg ACTLR2_S r
  else (ACTLR2_NS_write r)

def __set_CPACR (value_name : (BitVec 32)) : SailM Unit := do
  let r : CPACR_Type := value_name
  (CPACR_write (Mk_CPACR_Type (set_slice 20 (← (CPACR_read__1 ())) 0 (BitVec.slice r 0 20))))
  (CPACR_write (Mk_CPACR_Type (set_slice 8 (← (CPACR_read__1 ())) 24 (BitVec.slice r 24 8))))
  if ((! (←((pure (HaveEL EL3)) <&&> (do
         (ELUsingAArch32 EL3)) <&&> (do
         (pure (! (← (IsCurrentSecurityState SS_Secure))))) <&&> (do
         (pure ((_get_NSACR_Type_cp10 (← readReg NSACR)) == 0#1)))))) : Bool)
  then (CPACR_write (_update_CPACR_Type_cp11 (← (CPACR_read__1 ())) (_get_CPACR_Type_cp11 r)))
  else (pure ())
  if ((! (←((pure (HaveEL EL3)) <&&> (do
         (ELUsingAArch32 EL3)) <&&> (do
         (pure (! (← (IsCurrentSecurityState SS_Secure))))) <&&> (do
         (pure ((_get_NSACR_Type_cp10 (← readReg NSACR)) == 0#1)))))) : Bool)
  then (CPACR_write (_update_CPACR_Type_cp10 (← (CPACR_read__1 ())) (_get_CPACR_Type_cp10 r)))
  else (pure ())

def __set_SCTLR_S (value_name : (BitVec 32)) : SailM Unit := do
  let r : SCTLR_Type := value_name
  writeReg SCTLR_S (Sail.BitVec.updateSubrange (← readReg SCTLR_S) 4 0 (BitVec.slice r 0 5))
  writeReg SCTLR_S (BitVec.update (← readReg SCTLR_S) 6 (Bit (BitVec.slice r 6 1)))
  writeReg SCTLR_S (Sail.BitVec.updateSubrange (← readReg SCTLR_S) 31 8 (BitVec.slice r 8 24))
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_ITD")))) : Bool)
  then writeReg SCTLR_S (Sail.BitVec.updateSubrange (← readReg SCTLR_S) 7 7 (_get_SCTLR_Type_ITD r))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_CP15BEN")))) : Bool)
  then writeReg SCTLR_S (Sail.BitVec.updateSubrange (← readReg SCTLR_S) 5 5 (_get_SCTLR_Type_CP15BEN r))
  else (pure ())

def __set_SCTLR_NS (value_name : (BitVec 32)) : SailM Unit := do
  let r : SCTLR_Type := value_name
  (SCTLR_NS_write (Mk_SCTLR_Type (set_slice 5 (← (SCTLR_NS_read ())) 0 (BitVec.slice r 0 5))))
  (SCTLR_NS_write (Mk_SCTLR_Type (set_slice 1 (← (SCTLR_NS_read ())) 6 (BitVec.slice r 6 1))))
  (SCTLR_NS_write (Mk_SCTLR_Type (set_slice 24 (← (SCTLR_NS_read ())) 8 (BitVec.slice r 8 24))))
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_ITD")))) : Bool)
  then (SCTLR_NS_write (_update_SCTLR_Type_ITD (← (SCTLR_NS_read ())) (_get_SCTLR_Type_ITD r)))
  else (pure ())
  if ((! (! (← (__IMPDEF_boolean "IMPLEMENTED_CP15BEN")))) : Bool)
  then (SCTLR_NS_write (_update_SCTLR_Type_CP15BEN (← (SCTLR_NS_read ())) (_get_SCTLR_Type_CP15BEN r)))
  else (pure ())

def __set_DBGDSCRext (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDSCRext_Type := value_name
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 6 (← (DBGDSCRext_read ())) 0 (BitVec.slice r 0 6))))
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 7 (← (DBGDSCRext_read ())) 7 (BitVec.slice r 7 7))))
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 1 (← (DBGDSCRext_read ())) 15 (BitVec.slice r 15 1))))
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 1 (← (DBGDSCRext_read ())) 20 (BitVec.slice r 20 1))))
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 2 (← (DBGDSCRext_read ())) 24 (BitVec.slice r 24 2))))
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 1 (← (DBGDSCRext_read ())) 28 (BitVec.slice r 28 1))))
  if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
  then (DBGDSCRext_write (_update_DBGDSCRext_Type_TFO (← (DBGDSCRext_read ())) (_get_DBGDSCRext_Type_TFO r)))
  else (pure ())
  if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
  then (DBGDSCRext_write (_update_DBGDSCRext_Type_RXfull (← (DBGDSCRext_read ())) (_get_DBGDSCRext_Type_RXfull r)))
  else (pure ())
  if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
  then (DBGDSCRext_write (_update_DBGDSCRext_Type_TXfull (← (DBGDSCRext_read ())) (_get_DBGDSCRext_Type_TXfull r)))
  else (pure ())
  if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
  then (DBGDSCRext_write (_update_DBGDSCRext_Type_RXO (← (DBGDSCRext_read ())) (_get_DBGDSCRext_Type_RXO r)))
  else (pure ())
  if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
  then (DBGDSCRext_write (_update_DBGDSCRext_Type_TXU (← (DBGDSCRext_read ())) (_get_DBGDSCRext_Type_TXU r)))
  else (pure ())
  if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
  then (DBGDSCRext_write (_update_DBGDSCRext_Type_INTdis (← (DBGDSCRext_read ())) (_get_DBGDSCRext_Type_INTdis r)))
  else (pure ())
  if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
  then (DBGDSCRext_write (_update_DBGDSCRext_Type_TDA (← (DBGDSCRext_read ())) (_get_DBGDSCRext_Type_TDA r)))
  else (pure ())
  if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
  then (DBGDSCRext_write (_update_DBGDSCRext_Type_SC2 (← (DBGDSCRext_read ())) (_get_DBGDSCRext_Type_SC2 r)))
  else (pure ())
  if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
  then (DBGDSCRext_write (_update_DBGDSCRext_Type_HDE (← (DBGDSCRext_read ())) (_get_DBGDSCRext_Type_HDE r)))
  else (pure ())
  if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
  then (DBGDSCRext_write (_update_DBGDSCRext_Type_ERR (← (DBGDSCRext_read ())) (_get_DBGDSCRext_Type_ERR r)))
  else (pure ())

def _set_DBGDIDR_Type_SE_imp (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDIDR_Type_SE_imp r v)

def _set_DBGDIDR_Type_Version (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDIDR_Type_Version r v)

def _set_DBGDIDR_Type_nSUHD_imp (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDIDR_Type_nSUHD_imp r v)

def __set_CNTP_CTL_NS (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTP_CTL_Type := value_name
  (CNTP_CTL_NS_write (Mk_CNTP_CTL_Type (set_slice 2 (← (CNTP_CTL_NS_read ())) 0 (BitVec.slice r 0 2))))
  (CNTP_CTL_NS_write (Mk_CNTP_CTL_Type (set_slice 29 (← (CNTP_CTL_NS_read ())) 3 (BitVec.slice r 3 29))))

def TPIDRPRW_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM TPIDRPRW_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg TPIDRPRW_S)
  else (do (TPIDRPRW_NS_read ()))

def TPIDRPRW_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRPRW_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg TPIDRPRW_S r
  else (TPIDRPRW_NS_write r)

def IFAR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM IFAR_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do (IFAR_S_read ()))
  else (do (IFAR_NS_read ()))

def __get_selected_PMEVTYPER (_ : Unit) : SailM (BitVec 32) := do
  let idx ← do (pure (BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))))
  sail_assert (idx ≤b 30) "src/v8_base.sail:51572.20-51572.21"
  (PMEVTYPER_read idx)

def __set_selected_PMEVTYPER (value_name : (BitVec 32)) : SailM Unit := do
  let idx ← do (pure (BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))))
  sail_assert (idx ≤b 30) "src/v8_base.sail:51580.20-51580.21"
  (PMEVTYPER_set idx value_name)

def __set_CNTV_CTL (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTV_CTL_Type := value_name
  (CNTV_CTL_write (Mk_CNTV_CTL_Type (set_slice 2 (← (CNTV_CTL_read ())) 0 (BitVec.slice r 0 2))))
  (CNTV_CTL_write (Mk_CNTV_CTL_Type (set_slice 29 (← (CNTV_CTL_read ())) 3 (BitVec.slice r 3 29))))

def CONTEXTIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CONTEXTIDR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg CONTEXTIDR_S r
  else (CONTEXTIDR_NS_write r)

def DFAR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM DFAR_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do (DFAR_S_read ()))
  else (do (DFAR_NS_read ()))

def __set_CNTHP_CTL (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHP_CTL_Type := value_name
  (CNTHP_CTL_write (Mk_CNTHP_CTL_Type (set_slice 2 (← (CNTHP_CTL_read ())) 0 (BitVec.slice r 0 2))))
  (CNTHP_CTL_write (Mk_CNTHP_CTL_Type (set_slice 29 (← (CNTHP_CTL_read ())) 3 (BitVec.slice r 3 29))))

def AMAIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector 32) ) : SailM AMAIR1_Type )
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (do readReg AMAIR1_S)
  else (do (AMAIR1_NS_read ()))

def AMAIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMAIR1_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg AMAIR1_S r
  else (AMAIR1_NS_write r)

def _set_GICD_CTLR_Type_ARE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_ARE r v)

def _set_GICD_CTLR_Type_ARE_S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_ARE_S r v)

def _set_GICD_CTLR_Type_E1NWF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_E1NWF r v)

def _set_GICD_CTLR_Type_EnableGrp0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_EnableGrp0 r v)

def _set_GICC_CTLR_Type_EnableGrp0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_CTLR_Type_EnableGrp0 r v)

def _set_GICV_CTLR_Type_EnableGrp0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_CTLR_Type_EnableGrp0 r v)

def _set_GICD_CTLR_Type_EnableGrp1A (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_EnableGrp1A r v)

def _set_GICD_CTLR_Type_RWP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_RWP r v)

def _set_GICR_CTLR_Type_RWP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CTLR_Type_RWP r v)

def _set_GICD_CTLR_Type_nASSGIreq (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_CTLR_Type_nASSGIreq r v)

def _set_CTILAR_Type_KEY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTILAR_Type_KEY r v)

def _set_EDLAR_Type_KEY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDLAR_Type_KEY r v)

def _set_PMLAR_Type_KEY (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMLAR_Type_KEY r v)

def _set_CTIPIDR2_Type_DES_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR2_Type_DES_1 r v)

def _set_AMPIDR2_Type_DES_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR2_Type_DES_1 r v)

def _set_EDPIDR2_Type_DES_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR2_Type_DES_1 r v)

def _set_PMPIDR2_Type_DES_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR2_Type_DES_1 r v)

def _set_CTIPIDR2_Type_JEDEC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR2_Type_JEDEC r v)

def _set_AMPIDR2_Type_JEDEC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR2_Type_JEDEC r v)

def _set_EDPIDR2_Type_JEDEC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR2_Type_JEDEC r v)

def _set_PMPIDR2_Type_JEDEC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR2_Type_JEDEC r v)

def _set_CTIPIDR2_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR2_Type_REVISION r v)

def _set_AMDEVARCH_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMDEVARCH_Type_REVISION r v)

def _set_AMPIDR2_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR2_Type_REVISION r v)

def _set_CTIDEVARCH_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVARCH_Type_REVISION r v)

def _set_EDDEVARCH_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVARCH_Type_REVISION r v)

def _set_EDPIDR2_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR2_Type_REVISION r v)

def _set_PMPIDR2_Type_REVISION (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR2_Type_REVISION r v)

def _set_CTICIDR1_Type_CLASS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICIDR1_Type_CLASS r v)

def _set_AMCIDR1_Type_CLASS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCIDR1_Type_CLASS r v)

def _set_EDCIDR1_Type_CLASS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDCIDR1_Type_CLASS r v)

def _set_PMCIDR1_Type_CLASS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCIDR1_Type_CLASS r v)

def _set_CTICIDR1_Type_PRMBL_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICIDR1_Type_PRMBL_1 r v)

def _set_AMCIDR1_Type_PRMBL_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCIDR1_Type_PRMBL_1 r v)

def _set_EDCIDR1_Type_PRMBL_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDCIDR1_Type_PRMBL_1 r v)

def _set_PMCIDR1_Type_PRMBL_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCIDR1_Type_PRMBL_1 r v)

def _set_CTIDEVTYPE_Type_MAJOR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVTYPE_Type_MAJOR r v)

def _set_AMDEVTYPE_Type_MAJOR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMDEVTYPE_Type_MAJOR r v)

def _set_EDDEVTYPE_Type_MAJOR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVTYPE_Type_MAJOR r v)

def _set_PMDEVTYPE_Type_MAJOR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMDEVTYPE_Type_MAJOR r v)

def _set_CTIDEVTYPE_Type_SUB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVTYPE_Type_SUB r v)

def _set_AMDEVTYPE_Type_SUB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMDEVTYPE_Type_SUB r v)

def _set_EDDEVTYPE_Type_SUB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVTYPE_Type_SUB r v)

def _set_PMDEVTYPE_Type_SUB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMDEVTYPE_Type_SUB r v)

def _set_GITS_CTLR_Type_Enabled (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CTLR_Type_Enabled r v)

def _set_GITS_CTLR_Type_ITS_Number (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CTLR_Type_ITS_Number r v)

def _set_GITS_CTLR_Type_ImDe (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CTLR_Type_ImDe r v)

def _set_GITS_CTLR_Type_Quiescent (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_CTLR_Type_Quiescent r v)

def _set_EDDEVARCH_Type_ARCHITECT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 11)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVARCH_Type_ARCHITECT r v)

def _set_AMDEVARCH_Type_ARCHITECT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 11)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMDEVARCH_Type_ARCHITECT r v)

def _set_CTIDEVARCH_Type_ARCHITECT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 11)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVARCH_Type_ARCHITECT r v)

def _set_EDDEVARCH_Type_ARCHPART (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVARCH_Type_ARCHPART r v)

def _set_EDDEVARCH_Type_ARCHVER (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVARCH_Type_ARCHVER r v)

def _set_EDDEVARCH_Type_PRESENT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVARCH_Type_PRESENT r v)

def _set_AMDEVARCH_Type_PRESENT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMDEVARCH_Type_PRESENT r v)

def _set_CTIDEVARCH_Type_PRESENT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVARCH_Type_PRESENT r v)

def _set_CTIPIDR1_Type_DES_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR1_Type_DES_0 r v)

def _set_AMPIDR1_Type_DES_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR1_Type_DES_0 r v)

def _set_EDPIDR1_Type_DES_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR1_Type_DES_0 r v)

def _set_PMPIDR1_Type_DES_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR1_Type_DES_0 r v)

def _set_CTIPIDR1_Type_PART_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR1_Type_PART_1 r v)

def _set_AMPIDR1_Type_PART_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR1_Type_PART_1 r v)

def _set_EDPIDR1_Type_PART_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR1_Type_PART_1 r v)

def _set_PMPIDR1_Type_PART_1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR1_Type_PART_1 r v)

def _set_CNTSR_Type_DBGH (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTSR_Type_DBGH r v)

def _set_CNTSR_Type_FCACK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 10)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTSR_Type_FCACK r v)

def _set_EDCIDR3_Type_PRMBL_3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDCIDR3_Type_PRMBL_3 r v)

def _set_AMCIDR3_Type_PRMBL_3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCIDR3_Type_PRMBL_3 r v)

def _set_CTICIDR3_Type_PRMBL_3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICIDR3_Type_PRMBL_3 r v)

def _set_PMCIDR3_Type_PRMBL_3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCIDR3_Type_PRMBL_3 r v)

def _set_GICR_WAKER_Type_ChildrenAsleep (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_WAKER_Type_ChildrenAsleep r v)

def _set_GICR_WAKER_Type_ProcessorSleep (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_WAKER_Type_ProcessorSleep r v)

def _set_GITS_PARTIDR_Type_PARTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_PARTIDR_Type_PARTID r v)

def _set_GICR_PARTIDR_Type_PARTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PARTIDR_Type_PARTID r v)

def _set_GITS_PARTIDR_Type_PMG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_PARTIDR_Type_PMG r v)

def _set_GICR_PARTIDR_Type_PMG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_PARTIDR_Type_PMG r v)

def _set_CTIPIDR0_Type_PART_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR0_Type_PART_0 r v)

def _set_AMPIDR0_Type_PART_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR0_Type_PART_0 r v)

def _set_EDPIDR0_Type_PART_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR0_Type_PART_0 r v)

def _set_PMPIDR0_Type_PART_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR0_Type_PART_0 r v)

def _set_EDPIDR3_Type_CMOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR3_Type_CMOD r v)

def _set_AMPIDR3_Type_CMOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR3_Type_CMOD r v)

def _set_CTIPIDR3_Type_CMOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR3_Type_CMOD r v)

def _set_PMPIDR3_Type_CMOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR3_Type_CMOD r v)

def _set_EDPIDR3_Type_REVAND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR3_Type_REVAND r v)

def _set_AMPIDR3_Type_REVAND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR3_Type_REVAND r v)

def _set_CTIPIDR3_Type_REVAND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR3_Type_REVAND r v)

def _set_PMPIDR3_Type_REVAND (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR3_Type_REVAND r v)

def _set_GICC_STATUSR_Type_ASV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_STATUSR_Type_ASV r v)

def _set_GICC_STATUSR_Type_RRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_STATUSR_Type_RRD r v)

def _set_GICD_STATUSR_Type_RRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_STATUSR_Type_RRD r v)

def _set_GICR_STATUSR_Type_RRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_STATUSR_Type_RRD r v)

def _set_GICV_STATUSR_Type_RRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_STATUSR_Type_RRD r v)

def _set_GITS_STATUSR_Type_RRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_STATUSR_Type_RRD r v)

def _set_GICC_STATUSR_Type_RWOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_STATUSR_Type_RWOD r v)

def _set_GICD_STATUSR_Type_RWOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_STATUSR_Type_RWOD r v)

def _set_GICR_STATUSR_Type_RWOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_STATUSR_Type_RWOD r v)

def _set_GICV_STATUSR_Type_RWOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_STATUSR_Type_RWOD r v)

def _set_GITS_STATUSR_Type_RWOD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_STATUSR_Type_RWOD r v)

def _set_GICC_STATUSR_Type_WRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_STATUSR_Type_WRD r v)

def _set_GICD_STATUSR_Type_WRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_STATUSR_Type_WRD r v)

def _set_GICR_STATUSR_Type_WRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_STATUSR_Type_WRD r v)

def _set_GICV_STATUSR_Type_WRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_STATUSR_Type_WRD r v)

def _set_GITS_STATUSR_Type_WRD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_STATUSR_Type_WRD r v)

def _set_GICC_STATUSR_Type_WROD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_STATUSR_Type_WROD r v)

def _set_GICD_STATUSR_Type_WROD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_STATUSR_Type_WROD r v)

def _set_GICR_STATUSR_Type_WROD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_STATUSR_Type_WROD r v)

def _set_GICV_STATUSR_Type_WROD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_STATUSR_Type_WROD r v)

def _set_GITS_STATUSR_Type_WROD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_STATUSR_Type_WROD r v)

def _set_GICM_TYPER_Type_CLR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_TYPER_Type_CLR r v)

def _set_GICM_TYPER_Type_NumSPIs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 11)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICM_TYPER_Type_NumSPIs r v)

def _set_GICD_TYPER2_Type_VID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER2_Type_VID r v)

def _set_GICD_TYPER2_Type_VIL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER2_Type_VIL r v)

def _set_GICD_TYPER2_Type_nASSGIcap (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER2_Type_nASSGIcap r v)

def _set_GICV_ABPR_Type_Binary_Point (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_ABPR_Type_Binary_Point r v)

def _set_GICC_ABPR_Type_Binary_Point (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_ABPR_Type_Binary_Point r v)

def _set_GICC_BPR_Type_Binary_Point (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_BPR_Type_Binary_Point r v)

def _set_GICV_BPR_Type_Binary_Point (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_BPR_Type_Binary_Point r v)

def _set_CTIDEVARCH_Type_ARCHID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVARCH_Type_ARCHID r v)

def _set_AMDEVARCH_Type_ARCHID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMDEVARCH_Type_ARCHID r v)

def _set_GICR_MPAMIDR_Type_PARTIDmax (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_MPAMIDR_Type_PARTIDmax r v)

def _set_GITS_MPAMIDR_Type_PARTIDmax (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_MPAMIDR_Type_PARTIDmax r v)

def _set_GICR_MPAMIDR_Type_PMGmax (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_MPAMIDR_Type_PMGmax r v)

def _set_GITS_MPAMIDR_Type_PMGmax (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_MPAMIDR_Type_PMGmax r v)

def _set_GICR_CTLR_Type_CES (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CTLR_Type_CES r v)

def _set_GICR_CTLR_Type_DPG0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CTLR_Type_DPG0 r v)

def _set_GICR_CTLR_Type_DPG1NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CTLR_Type_DPG1NS r v)

def _set_GICR_CTLR_Type_DPG1S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CTLR_Type_DPG1S r v)

def _set_GICR_CTLR_Type_EnableLPIs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CTLR_Type_EnableLPIs r v)

def _set_GICR_CTLR_Type_UWP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_CTLR_Type_UWP r v)

def _set_CNTFID0_Type_Frequency (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTFID0_Type_Frequency r v)

def _set_GICD_TYPER_Type_CPUNumber (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_CPUNumber r v)

def _set_GICD_TYPER_Type_DVIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_DVIS r v)

def _set_GICD_TYPER_Type_ESPI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_ESPI r v)

def _set_GICD_TYPER_Type_ESPI_range (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_ESPI_range r v)

def _set_GICD_TYPER_Type_ITLinesNumber (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_ITLinesNumber r v)

def _set_GICD_TYPER_Type_LPIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_LPIS r v)

def _set_GICD_TYPER_Type_MBIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_MBIS r v)

def _set_GICD_TYPER_Type_No1N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_No1N r v)

def _set_GICD_TYPER_Type_SecurityExtn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_SecurityExtn r v)

def _set_GICD_TYPER_Type_num_LPIs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_TYPER_Type_num_LPIs r v)

def _set_CTICIDR0_Type_PRMBL_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICIDR0_Type_PRMBL_0 r v)

def _set_AMCIDR0_Type_PRMBL_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCIDR0_Type_PRMBL_0 r v)

def _set_EDCIDR0_Type_PRMBL_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDCIDR0_Type_PRMBL_0 r v)

def _set_PMCIDR0_Type_PRMBL_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCIDR0_Type_PRMBL_0 r v)

def _set_CTIITCTRL_Type_IME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIITCTRL_Type_IME r v)

def _set_EDITCTRL_Type_IME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDITCTRL_Type_IME r v)

def _set_PMITCTRL_Type_IME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMITCTRL_Type_IME r v)

def _set_GITS_STATUSR_Type_Overflow (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_STATUSR_Type_Overflow r v)

def _set_GITS_STATUSR_Type_Syndrome (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GITS_STATUSR_Type_Syndrome r v)

def _set_GICC_CTLR_Type_EOImodeS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_CTLR_Type_EOImodeS r v)

def _set_GICC_CTLR_Type_FIQBypDisGrp0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_CTLR_Type_FIQBypDisGrp0 r v)

def _set_GICC_CTLR_Type_FIQEn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_CTLR_Type_FIQEn r v)

def _set_GICV_CTLR_Type_FIQEn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_CTLR_Type_FIQEn r v)

def _set_GICC_CTLR_Type_IRQBypDisGrp0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICC_CTLR_Type_IRQBypDisGrp0 r v)

def _set_EDPIDR4_Type_DES_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPIDR4_Type_DES_2 r v)

def _set_AMPIDR4_Type_DES_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMPIDR4_Type_DES_2 r v)

def _set_CTIPIDR4_Type_DES_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIPIDR4_Type_DES_2 r v)

def _set_PMPIDR4_Type_DES_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMPIDR4_Type_DES_2 r v)

def _set_CTICONTROL_Type_GLBEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICONTROL_Type_GLBEN r v)

def _set_GICR_INMIR0_Type_nmi0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi0 r v)

def _set_GICR_INMIR0_Type_nmi1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi1 r v)

def _set_GICR_INMIR0_Type_nmi10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi10 r v)

def _set_GICR_INMIR0_Type_nmi11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi11 r v)

def _set_GICR_INMIR0_Type_nmi12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi12 r v)

def _set_GICR_INMIR0_Type_nmi13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi13 r v)

def _set_GICR_INMIR0_Type_nmi14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi14 r v)

def _set_GICR_INMIR0_Type_nmi15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi15 r v)

def _set_GICR_INMIR0_Type_nmi16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi16 r v)

def _set_GICR_INMIR0_Type_nmi17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi17 r v)

def _set_GICR_INMIR0_Type_nmi18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi18 r v)

def _set_GICR_INMIR0_Type_nmi19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi19 r v)

def _set_GICR_INMIR0_Type_nmi2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi2 r v)

def _set_GICR_INMIR0_Type_nmi20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi20 r v)

def _set_GICR_INMIR0_Type_nmi21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi21 r v)

def _set_GICR_INMIR0_Type_nmi22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi22 r v)

def _set_GICR_INMIR0_Type_nmi23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi23 r v)

def _set_GICR_INMIR0_Type_nmi24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi24 r v)

def _set_GICR_INMIR0_Type_nmi25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi25 r v)

def _set_GICR_INMIR0_Type_nmi26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi26 r v)

def _set_GICR_INMIR0_Type_nmi27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi27 r v)

def _set_GICR_INMIR0_Type_nmi28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi28 r v)

def _set_GICR_INMIR0_Type_nmi29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi29 r v)

def _set_GICR_INMIR0_Type_nmi3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi3 r v)

def _set_GICR_INMIR0_Type_nmi30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi30 r v)

def _set_GICR_INMIR0_Type_nmi31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi31 r v)

def _set_GICR_INMIR0_Type_nmi4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi4 r v)

def _set_GICR_INMIR0_Type_nmi5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi5 r v)

def _set_GICR_INMIR0_Type_nmi6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi6 r v)

def _set_GICR_INMIR0_Type_nmi7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi7 r v)

def _set_GICR_INMIR0_Type_nmi8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi8 r v)

def _set_GICR_INMIR0_Type_nmi9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi9 r v)

def _set_GICV_CTLR_Type_AckCtl (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_CTLR_Type_AckCtl r v)

def _set_GICV_CTLR_Type_EnableGrp1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICV_CTLR_Type_EnableGrp1 r v)

def _set_EDDEVID1_Type_HSR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVID1_Type_HSR r v)

def _set_EDPRCR_Type_COREPURQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRCR_Type_COREPURQ r v)

def _set_EDPRCR_Type_CWRR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDPRCR_Type_CWRR r v)

def _set_GICR_VSGIPENDR_Type_Busy (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VSGIPENDR_Type_Busy r v)

def _set_GICR_SYNCR_Type_Busy (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_SYNCR_Type_Busy r v)

def _set_GICR_VSGIPENDR_Type_Pending (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_VSGIPENDR_Type_Pending r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit0 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit1 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit10 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit11 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit12 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit13 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit14 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit15 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit16 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit17 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit18 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit19 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit2 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit20 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit21 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit22 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit23 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit24 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit25 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit26 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit27 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit28 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit29 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit3 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit30 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit31 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit4 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit5 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit6 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit7 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit8 r v)

def _set_GICR_ISENABLER0_Type_Set_enable_bit9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit9 r v)

def _set_CTICIDR2_Type_PRMBL_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTICIDR2_Type_PRMBL_2 r v)

def _set_AMCIDR2_Type_PRMBL_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_AMCIDR2_Type_PRMBL_2 r v)

def _set_EDCIDR2_Type_PRMBL_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDCIDR2_Type_PRMBL_2 r v)

def _set_PMCIDR2_Type_PRMBL_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMCIDR2_Type_PRMBL_2 r v)

def _set_EDRCR_Type_CBRRQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDRCR_Type_CBRRQ r v)

def _set_EDRCR_Type_CSE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDRCR_Type_CSE r v)

def _set_EDRCR_Type_CSPA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDRCR_Type_CSPA r v)

def _set_EDDEVID_Type_DebugPower (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDDEVID_Type_DebugPower r v)

def _set_GICD_SGIR_Type_CPUTargetList (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_SGIR_Type_CPUTargetList r v)

def _set_GICD_SGIR_Type_NSATT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_SGIR_Type_NSATT r v)

def _set_GICD_SGIR_Type_TargetListFilter (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICD_SGIR_Type_TargetListFilter r v)

def _set_CNTID_Type_CNTSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTID_Type_CNTSC r v)

def _set_GICH_HCR_Type_EOICount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_GICH_HCR_Type_EOICount r v)

def _set_CTIDEVID_Type_EXTMUXNUM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVID_Type_EXTMUXNUM r v)

def _set_CTIDEVID_Type_INOUT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVID_Type_INOUT r v)

def _set_CTIDEVID_Type_NUMCHAN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVID_Type_NUMCHAN r v)

def _set_CTIDEVID_Type_NUMTRIG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CTIDEVID_Type_NUMTRIG r v)

def _set_CNTNSAR_Type_NS2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTNSAR_Type_NS2 r v)

def _set_CNTNSAR_Type_NS3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTNSAR_Type_NS3 r v)

def _set_CNTNSAR_Type_NS4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTNSAR_Type_NS4 r v)

def _set_CNTNSAR_Type_NS5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTNSAR_Type_NS5 r v)

def _set_CNTNSAR_Type_NS6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTNSAR_Type_NS6 r v)

def _set_CNTNSAR_Type_NS7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTNSAR_Type_NS7 r v)

def __get_ID_AA64MMFR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64MMFR2_EL1_Type := value_name
  (Mk_ID_AA64MMFR2_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xF00000000000#48 64))))

def __get_VTCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VTCR_EL2_Type := value_name
  (Mk_VTCR_EL2_Type ((tmp &&& (Complement.complement 0xFFFFEC8001900000#64)) ||| (Sail.BitVec.zeroExtend 0x80000000#32 64)))

def __get_HDFGRTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HDFGRTR_EL2_Type := value_name
  (Mk_HDFGRTR_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1FE04C000300100#60 64))))

def __get_ICV_NMIAR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_NMIAR1_EL1_Type := value_name
  (Mk_ICV_NMIAR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_SPSR_abt (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_abt_Type := value_name
  (Mk_SPSR_abt_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_ICH_LR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_LR_EL2_Type := value_name
  (Mk_ICH_LR_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x700E00000000000#60 64))))

def __get_MDCCINT_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDCCINT_EL1_Type := value_name
  (Mk_MDCCINT_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF9FFFFFFF#64)))

def __get_ICC_HPPIR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_HPPIR1_EL1_Type := value_name
  (Mk_ICC_HPPIR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_TCR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TCR2_EL2_Type := value_name
  (Mk_TCR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_ICV_BPR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_BPR1_EL1_Type := value_name
  (Mk_ICV_BPR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_TCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TCR_EL3_Type := value_name
  (Mk_TCR_EL3_Type ((tmp &&& (Complement.complement 0xFFFFF180000800C0#64)) ||| (Sail.BitVec.zeroExtend 0x80800000#32 64)))

def __get_PMECR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMECR_EL1_Type := value_name
  (Mk_PMECR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFE0#64)))

def __get_RMR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : RMR_EL1_Type := value_name
  (Mk_RMR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))

def __get_PMICFILTR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMICFILTR_EL0_Type := value_name
  (Mk_PMICFILTR_EL0_Type (tmp &&& (Complement.complement 0xFBFFFFFF020F0000#64)))

def __get_ICC_HPPIR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_HPPIR0_EL1_Type := value_name
  (Mk_ICC_HPPIR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_CNTHPS_CTL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHPS_CTL_EL2_Type := value_name
  (Mk_CNTHPS_CTL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_VMECID_A_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VMECID_A_EL2_Type := value_name
  (Mk_VMECID_A_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_MECID_RL_A_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECID_RL_A_EL3_Type := value_name
  (Mk_MECID_RL_A_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_HSTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HSTR_EL2_Type := value_name
  (Mk_HSTR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF4010#64)))

def __get_PMOVSCLR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMOVSCLR_EL0_Type := value_name
  (Mk_PMOVSCLR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))

def __get_HAFGRTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HAFGRTR_EL2_Type := value_name
  (Mk_HAFGRTR_EL2_Type (tmp &&& (Complement.complement 0xFFFC00000001FFE0#64)))

def __get_ICC_BPR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_BPR0_EL1_Type := value_name
  (Mk_ICC_BPR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_ACCDATA_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ACCDATA_EL1_Type := value_name
  (Mk_ACCDATA_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_OSDLR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : OSDLR_EL1_Type := value_name
  let tmp ← (( do
    if ((! (← (IsFeatureImplemented FEAT_DoubleLock))) : Bool)
    then (pure (Mk_OSDLR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1#4 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  (pure (Mk_OSDLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64))))

def __get_SCTLR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : SCTLR_EL1_Type := value_name
  let tmp : SCTLR_EL1_Type := (Mk_SCTLR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x400020000#36 64))))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_CP15BEN"))) : Bool)
    then (pure (Mk_SCTLR_EL1_Type ((tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x0#4 64))) ||| (Sail.BitVec.zeroExtend 0x20#8 64))))
    else (pure tmp) ) : SailM (BitVec 64) )
  if ((! (← (__IMPDEF_boolean "IMPLEMENTED_ITD"))) : Bool)
  then (pure (Mk_SCTLR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x80#8 64)))))
  else (pure tmp)

def __get_PMSSCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSSCR_EL1_Type := value_name
  (Mk_PMSSCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFEFFFFFFFE#64)))

def __get_LORID_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : LORID_EL1_Type := value_name
  (Mk_LORID_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FF00#64)))

def __get_CONTEXTIDR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CONTEXTIDR_EL2_Type := value_name
  (Mk_CONTEXTIDR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_CNTP_TVAL_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTP_TVAL_EL0_Type := value_name
  (Mk_CNTP_TVAL_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_ID_AA64MMFR4_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64MMFR4_EL1_Type := value_name
  (Mk_ID_AA64MMFR4_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF0F#64)))

def __get_ICH_EISR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_EISR_EL2_Type := value_name
  (Mk_ICH_EISR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_MIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MIDR_EL1_Type := value_name
  (Mk_MIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_ICC_RPR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_RPR_EL1_Type := value_name
  (Mk_ICC_RPR_EL1_Type (tmp &&& (Complement.complement 0x3FFFFFFFFFFFFF00#64)))

def __get_ICH_ELRSR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_ELRSR_EL2_Type := value_name
  (Mk_ICH_ELRSR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_HFGITR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGITR_EL2_Type := value_name
  (Mk_HFGITR_EL2_Type (tmp &&& (Complement.complement 0xE000000000000000#64)))

def __get_CNTHVS_CTL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHVS_CTL_EL2_Type := value_name
  (Mk_CNTHVS_CTL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_ID_AA64PFR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64PFR1_EL1_Type := value_name
  (Mk_ID_AA64PFR1_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xF00000#24 64))))

def __get_ICH_AP1R_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_AP1R_EL2_Type := value_name
  (Mk_ICH_AP1R_EL2_Type (tmp &&& (Complement.complement 0x7FFFFFFF00000000#64)))

def __get_SDER32_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SDER32_EL2_Type := value_name
  (Mk_SDER32_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))

def __get_VSTCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VSTCR_EL2_Type := value_name
  (Mk_VSTCR_EL2_Type ((tmp &&& (Complement.complement 0xFFFFFFFD1FFF3F00#64)) ||| (Sail.BitVec.zeroExtend 0x80000000#32 64)))

def __get_ID_AA64ISAR0_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : ID_AA64ISAR0_EL1_Type := value_name
  let tmp : ID_AA64ISAR0_EL1_Type := (Mk_ID_AA64ISAR0_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xF#4 64))))
  if ((←((pure ((← readReg PSTATE).EL == EL2)) <||> (do
       (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
       (pure ((_get_SCR_EL3_Type_TME (← readReg SCR_EL3)) == 0#1))) <||> (do
       (pure ((← readReg PSTATE).EL == EL1)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure ((_get_HCR_EL2_Type_TME (← readReg HCR_EL2)) == 0#1)))))) : Bool)
  then (pure (Mk_ID_AA64ISAR0_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xF000000#28 64)))))
  else (pure tmp)

def __get_PMMIR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMMIR_EL1_Type := value_name
  (Mk_PMMIR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFF0000000#64)))

def __get_ICV_IAR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_IAR0_EL1_Type := value_name
  (Mk_ICV_IAR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_ICC_IGRPEN1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IGRPEN1_EL1_Type := value_name
  (Mk_ICC_IGRPEN1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))

def __get_ICC_IGRPEN1_EL1_NS (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IGRPEN1_EL1_Type := value_name
  (Mk_ICC_IGRPEN1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))

def __get_ICC_IGRPEN1_EL1_S (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IGRPEN1_EL1_Type := value_name
  (Mk_ICC_IGRPEN1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))

def __get_GPTBR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GPTBR_EL3_Type := value_name
  (Mk_GPTBR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFF0000000000#64)))

def __get_MDCCSR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDCCSR_EL0_Type := value_name
  (Mk_MDCCSR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF9FFFFFFF#64)))

def __get_TTBR0_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TTBR0_EL3_Type := value_name
  (Mk_TTBR0_EL3_Type (tmp &&& (Complement.complement 0xFF00000000000000#64)))

def __get_DBGBCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGBCR_EL1_Type := value_name
  (Mk_DBGBCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00001E10#64)))

def __get_PMCCFILTR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMCCFILTR_EL0_Type := value_name
  (Mk_PMCCFILTR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF020FFFFF#64)))

def __get_ICC_NMIAR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_NMIAR1_EL1_Type := value_name
  (Mk_ICC_NMIAR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_DBGCLAIMSET_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGCLAIMSET_EL1_Type := value_name
  (Mk_DBGCLAIMSET_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))

def __get_ICC_SRE_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_SRE_EL1_Type := value_name
  (Mk_ICC_SRE_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_ICC_SRE_EL1_NS (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_SRE_EL1_Type := value_name
  (Mk_ICC_SRE_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_ICC_SRE_EL1_S (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_SRE_EL1_Type := value_name
  (Mk_ICC_SRE_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_ICH_AP0R_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_AP0R_EL2_Type := value_name
  (Mk_ICH_AP0R_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_ICC_IAR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IAR0_EL1_Type := value_name
  (Mk_ICC_IAR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_CONTEXTIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CONTEXTIDR_EL1_Type := value_name
  (Mk_CONTEXTIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_PMUACR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMUACR_EL1_Type := value_name
  (Mk_PMUACR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))

def __get_RMR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : RMR_EL2_Type := value_name
  (Mk_RMR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))

def __get_VNCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VNCR_EL2_Type := value_name
  (Mk_VNCR_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xFFF#12 64))))

def __get_PMINTENCLR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMINTENCLR_EL1_Type := value_name
  (Mk_PMINTENCLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))

def __get_PMSELR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSELR_EL0_Type := value_name
  (Mk_PMSELR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFE0#64)))

def __get_ICC_CTLR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_CTLR_EL1_Type := value_name
  (Mk_ICC_CTLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF300BC#64)))

def __get_ICC_CTLR_EL1_NS (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_CTLR_EL1_Type := value_name
  (Mk_ICC_CTLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF300BC#64)))

def __get_ICC_CTLR_EL1_S (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_CTLR_EL1_Type := value_name
  (Mk_ICC_CTLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF300BC#64)))

def __get_ICC_AP1R_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_AP1R_EL1_Type := value_name
  (Mk_ICC_AP1R_EL1_Type (tmp &&& (Complement.complement 0x7FFFFFFF00000000#64)))

def __get_ICC_AP1R_EL1_NS (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_AP1R_EL1_Type := value_name
  (Mk_ICC_AP1R_EL1_Type (tmp &&& (Complement.complement 0x7FFFFFFF00000000#64)))

def __get_ICC_AP1R_EL1_S (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_AP1R_EL1_Type := value_name
  (Mk_ICC_AP1R_EL1_Type (tmp &&& (Complement.complement 0x7FFFFFFF00000000#64)))

def __get_CNTP_CTL_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTP_CTL_EL0_Type := value_name
  (Mk_CNTP_CTL_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_CNTHV_TVAL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHV_TVAL_EL2_Type := value_name
  (Mk_CNTHV_TVAL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_SPSR_irq (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_irq_Type := value_name
  (Mk_SPSR_irq_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_ICH_MISR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_MISR_EL2_Type := value_name
  (Mk_ICH_MISR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))

def __get_CSSELR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CSSELR_EL1_Type := value_name
  (Mk_CSSELR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFE0#64)))

def __get_ICV_RPR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_RPR_EL1_Type := value_name
  (Mk_ICV_RPR_EL1_Type (tmp &&& (Complement.complement 0x7FFFFFFFFFFFFF00#64)))

def __get_ICV_PMR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_PMR_EL1_Type := value_name
  (Mk_ICV_PMR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))

def __get_SPSR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_EL2_Type := value_name
  (Mk_SPSR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFF800000000#64)))

def __get_TCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TCR_EL1_Type := value_name
  (Mk_TCR_EL1_Type (tmp &&& (Complement.complement 0xC000000800000000#64)))

def __get_ICV_HPPIR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_HPPIR0_EL1_Type := value_name
  (Mk_ICV_HPPIR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_SCTLR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCTLR2_EL1_Type := value_name
  (Mk_SCTLR2_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF83#64)))

def __get_ICV_BPR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_BPR0_EL1_Type := value_name
  (Mk_ICV_BPR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_ISR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ISR_EL1_Type := value_name
  (Mk_ISR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFF83F#64)))

def __get_MECIDR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECIDR_EL2_Type := value_name
  (Mk_MECIDR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_PMINTENSET_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMINTENSET_EL1_Type := value_name
  (Mk_PMINTENSET_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))

def __get_SMIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SMIDR_EL1_Type := value_name
  (Mk_SMIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00007000#64)))

def __get_HFGWTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGWTR_EL2_Type := value_name
  (Mk_HFGWTR_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x845001624C604#52 64))))

def __get_SMPRI_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SMPRI_EL1_Type := value_name
  (Mk_SMPRI_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_PMUSERENR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMUSERENR_EL0_Type := value_name
  (Mk_PMUSERENR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF80#64)))

def __get_SCTLR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCTLR2_EL2_Type := value_name
  (Mk_SCTLR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF81#64)))

def __get_PMOVSSET_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMOVSSET_EL0_Type := value_name
  (Mk_PMOVSSET_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))

def __get_SCTLR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCTLR_EL3_Type := value_name
  (Mk_SCTLR_EL3_Type ((tmp &&& (Complement.complement 0x97D7E4CF0512C780#64)) ||| (Sail.BitVec.zeroExtend 0x30850030#32 64)))

def __get_ICV_CTLR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_CTLR_EL1_Type := value_name
  (Mk_ICV_CTLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF300FC#64)))

def __get_MECID_A0_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECID_A0_EL2_Type := value_name
  (Mk_MECID_A0_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_ICV_IAR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_IAR1_EL1_Type := value_name
  (Mk_ICV_IAR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_CPACR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CPACR_EL1_Type := value_name
  (Mk_CPACR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF4CCCFFFF#64)))

def __get_SPSR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_EL1_Type := value_name
  (Mk_SPSR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFF800000000#64)))

def __get_FPEXC32_EL2 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : FPEXC32_EL2_Type := value_name
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions"))) : Bool)
    then (pure (Mk_FPEXC32_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1#4 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions"))) : Bool)
    then (pure (Mk_FPEXC32_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x2#4 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions"))) : Bool)
    then (pure (Mk_FPEXC32_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x4#4 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions"))) : Bool)
    then (pure (Mk_FPEXC32_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x8#4 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions"))) : Bool)
    then (pure (Mk_FPEXC32_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x10#8 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp : FPEXC32_EL2_Type := (Mk_FPEXC32_EL2_Type ((tmp &&& (Complement.complement 0xFFFFFFFF9BFFF860#64)) ||| (Sail.BitVec.zeroExtend 0x700#12 64)))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions"))) : Bool)
    then (pure (Mk_FPEXC32_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x80#8 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of floating-point exceptions"))) : Bool)
  then (pure (Mk_FPEXC32_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x4000000#28 64)))))
  else (pure tmp)

def __get_MDSCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDSCR_EL1_Type := value_name
  (Mk_MDSCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFF213100F82#64)))

def __get_SPSR_fiq (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_fiq_Type := value_name
  (Mk_SPSR_fiq_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_MECID_P0_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECID_P0_EL2_Type := value_name
  (Mk_MECID_P0_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_GPCCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GPCCR_EL3_Type := value_name
  (Mk_GPCCR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF0C00F8#64)))

def __get_HDFGWTR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HDFGWTR2_EL2_Type := value_name
  (Mk_HDFGWTR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFD60040#64)))

def __get_TCR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TCR2_EL1_Type := value_name
  (Mk_TCR2_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF33C0#64)))

def __get_DCZID_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DCZID_EL0_Type := value_name
  (Mk_DCZID_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFE0#64)))

def __get_VSTTBR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VSTTBR_EL2_Type := value_name
  (Mk_VSTTBR_EL2_Type (tmp &&& (Complement.complement 0xFF00000000000000#64)))

def __get_TRFCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TRFCR_EL2_Type := value_name
  (Mk_TRFCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF94#64)))

def __get_CNTHP_CTL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHP_CTL_EL2_Type := value_name
  (Mk_CNTHP_CTL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_CNTHVS_TVAL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHVS_TVAL_EL2_Type := value_name
  (Mk_CNTHVS_TVAL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_CNTHP_TVAL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHP_TVAL_EL2_Type := value_name
  (Mk_CNTHP_TVAL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_CNTHCTL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHCTL_EL2_Type := value_name
  (Mk_CNTHCTL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF00000#64)))

def __get_MDRAR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDRAR_EL1_Type := value_name
  (Mk_MDRAR_EL1_Type (tmp &&& (Complement.complement 0xFF00000000000FFC#64)))

def __get_IFSR32_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : IFSR32_EL2_Type := value_name
  (Mk_IFSR32_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFEE9C0#64)))

def __get_ICC_IGRPEN1_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IGRPEN1_EL3_Type := value_name
  (Mk_ICC_IGRPEN1_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))

def __get_LORSA_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : LORSA_EL1_Type := value_name
  (Mk_LORSA_EL1_Type (tmp &&& (Complement.complement 0xFF0000000000FFFE#64)))

def __get_DBGWCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGWCR_EL1_Type := value_name
  (Mk_DBGWCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00E00000#64)))

def __get_PMEVTYPER_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMEVTYPER_EL0_Type := value_name
  (Mk_PMEVTYPER_EL0_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xBFFF000000F0000#60 64))))

def __get_CNTV_CTL_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTV_CTL_EL0_Type := value_name
  (Mk_CNTV_CTL_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_TRFCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TRFCR_EL1_Type := value_name
  (Mk_TRFCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF9C#64)))

def __get_ICH_VMCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_VMCR_EL2_Type := value_name
  (Mk_ICH_VMCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF0003FDE0#64)))

def __get_VPIDR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VPIDR_EL2_Type := value_name
  (Mk_VPIDR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_ICC_CTLR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_CTLR_EL3_Type := value_name
  (Mk_ICC_CTLR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF10080#64)))

def __get_SCTLR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCTLR_EL2_Type := value_name
  (Mk_SCTLR_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x400020200#36 64))))

def __get_OSLSR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : OSLSR_EL1_Type := value_name
  (Mk_OSLSR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_MDCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDCR_EL3_Type := value_name
  (Mk_MDCR_EL3_Type (tmp &&& (Complement.complement 0xFFFF80802740012A#64)))

def __get_SCTLR2_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCTLR2_EL3_Type := value_name
  (Mk_SCTLR2_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFE5#64)))

def __get_PMCNTENSET_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMCNTENSET_EL0_Type := value_name
  (Mk_PMCNTENSET_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))

def __get_ICC_SRE_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_SRE_EL2_Type := value_name
  (Mk_ICC_SRE_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_CNTPS_CTL_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTPS_CTL_EL1_Type := value_name
  (Mk_CNTPS_CTL_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_DACR32_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DACR32_EL2_Type := value_name
  (Mk_DACR32_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_LORC_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : LORC_EL1_Type := value_name
  (Mk_LORC_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFC02#64)))

def __get_ID_AA64PFR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64PFR2_EL1_Type := value_name
  (Mk_ID_AA64PFR2_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFF000#64)))

def __get_TCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TCR_EL2_Type := value_name
  (Mk_TCR_EL2_Type (tmp &&& (Complement.complement 0xC000000800000040#64)))

def __get_CCSIDR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CCSIDR2_EL1_Type := value_name
  (Mk_CCSIDR2_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_CTR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CTR_EL0_Type := value_name
  (Mk_CTR_EL0_Type ((tmp &&& (Complement.complement 0xFFFFFFC040003FF0#64)) ||| (Sail.BitVec.zeroExtend 0x80000000#32 64)))

def __get_SPSR_und (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_und_Type := value_name
  (Mk_SPSR_und_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_ID_AA64ISAR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64ISAR2_EL1_Type := value_name
  (Mk_ID_AA64ISAR2_EL1_Type (tmp &&& (Complement.complement 0xFF00F00000000000#64)))

def __get_CPTR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CPTR_EL3_Type := value_name
  (Mk_CPTR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFF3FEFEAFF#64)))

def __get_HFGRTR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGRTR2_EL2_Type := value_name
  (Mk_HFGRTR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_RMR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : RMR_EL3_Type := value_name
  (Mk_RMR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))

def __get_ICH_HCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_HCR_EL2_Type := value_name
  (Mk_ICH_HCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF07FF0200#64)))

def __get_ICC_IGRPEN0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IGRPEN0_EL1_Type := value_name
  (Mk_ICC_IGRPEN0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))

def __get_CNTHPS_TVAL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHPS_TVAL_EL2_Type := value_name
  (Mk_CNTHPS_TVAL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_ICC_BPR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_BPR1_EL1_Type := value_name
  (Mk_ICC_BPR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_ICC_BPR1_EL1_NS (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_BPR1_EL1_Type := value_name
  (Mk_ICC_BPR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_ICC_BPR1_EL1_S (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_BPR1_EL1_Type := value_name
  (Mk_ICC_BPR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_MECID_A1_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECID_A1_EL2_Type := value_name
  (Mk_MECID_A1_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_ID_AA64MMFR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64MMFR0_EL1_Type := value_name
  (Mk_ID_AA64MMFR0_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xFF000000000000#56 64))))

def __get_PMCR_EL0 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : PMCR_EL0_Type := value_name
  let tmp : PMCR_EL0_Type := (Mk_PMCR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000506#64)))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "the implementation includes a PMU event export bus"))) : Bool)
    then (pure (Mk_PMCR_EL0_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x10#8 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  if ((! (! (← (IsFeatureImplemented FEAT_PMUv3p7)))) : Bool)
  then (pure (Mk_PMCR_EL0_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xFF000000#32 64)))))
  else (pure tmp)

def __get_HDFGRTR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HDFGRTR2_EL2_Type := value_name
  (Mk_HDFGRTR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF00000#64)))

def __get_DBGPRCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGPRCR_EL1_Type := value_name
  (Mk_DBGPRCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))

def __get_PMCNTENCLR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMCNTENCLR_EL0_Type := value_name
  (Mk_PMCNTENCLR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000000#64)))

def __get_SDER32_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SDER32_EL3_Type := value_name
  (Mk_SDER32_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))

def __get_HPFAR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HPFAR_EL2_Type := value_name
  (Mk_HPFAR_EL2_Type (tmp &&& (Complement.complement 0x7FFF00000000000F#64)))

def __get_VMPIDR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VMPIDR_EL2_Type := value_name
  (Mk_VMPIDR_EL2_Type ((tmp &&& (Complement.complement 0xFFFFFF003E000000#64)) ||| (Sail.BitVec.zeroExtend 0x80000000#32 64)))

def __get_ID_AA64MMFR3_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64MMFR3_EL1_Type := value_name
  (Mk_ID_AA64MMFR3_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xF000000000000#52 64))))

def __get_ICH_VTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICH_VTR_EL2_Type := value_name
  (Mk_ICH_VTR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF0003FFE0#64)))

def __get_MDSELR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDSELR_EL1_Type := value_name
  (Mk_MDSELR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFCF#64)))

def __get_MDCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MDCR_EL2_Type := value_name
  (Mk_MDCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFF4EF03750000#64)))

def __get_CNTKCTL_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTKCTL_EL1_Type := value_name
  (Mk_CNTKCTL_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFDFC00#64)))

def __get_LORN_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : LORN_EL1_Type := value_name
  (Mk_LORN_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))

def __get_ICV_IGRPEN0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_IGRPEN0_EL1_Type := value_name
  (Mk_ICV_IGRPEN0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))

def __get_SPSR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPSR_EL3_Type := value_name
  (Mk_SPSR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFF800000000#64)))

def __get_CCSIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CCSIDR_EL1_Type := value_name
  (Mk_CCSIDR_EL1_Type (tmp &&& (Complement.complement 0xFF00000000000000#64)))

def __get_VMECID_P_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VMECID_P_EL2_Type := value_name
  (Mk_VMECID_P_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_OSECCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : OSECCR_EL1_Type := value_name
  (Mk_OSECCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_DBGVCR32_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGVCR32_EL2_Type := value_name
  (Mk_DBGVCR32_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF21FF2321#64)))

def __get_HFGRTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGRTR_EL2_Type := value_name
  (Mk_HFGRTR_EL2_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x8000000000000#52 64))))

def __get_CPTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CPTR_EL2_Type := value_name
  (Mk_CPTR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF0CCC4000#64)))

def __get_CLIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CLIDR_EL1_Type := value_name
  (Mk_CLIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFF800000000000#64)))

def __get_HCRX_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HCRX_EL2_Type := value_name
  (Mk_HCRX_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF803000#64)))

def __get_ICV_IGRPEN1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_IGRPEN1_EL1_Type := value_name
  (Mk_ICV_IGRPEN1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))

def __get_HFGWTR2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HFGWTR2_EL2_Type := value_name
  (Mk_HFGWTR2_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFA#64)))

def __get_MECID_P1_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MECID_P1_EL2_Type := value_name
  (Mk_MECID_P1_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_SPMSELR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SPMSELR_EL0_Type := value_name
  (Mk_SPMSELR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFC0C#64)))

def __get_DBGAUTHSTATUS_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGAUTHSTATUS_EL1_Type := value_name
  (Mk_DBGAUTHSTATUS_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFF0FF0F00#64)))

def __get_SCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCR_EL3_Type := value_name
  let tmp : SCR_EL3_Type := (Mk_SCR_EL3_Type ((tmp &&& (Complement.complement 0xB744000001C00040#64)) ||| (Sail.BitVec.zeroExtend 0x30#8 64)))
  if ((! ((HaveAArch32EL EL1) || (HaveAArch32EL EL2))) : Bool)
  then (Mk_SCR_EL3_Type ((tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x0#4 64))) ||| (Sail.BitVec.zeroExtend 0x400#12 64)))
  else tmp

def __get_ICC_SRE_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_SRE_EL3_Type := value_name
  (Mk_ICC_SRE_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_HDFGWTR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : HDFGWTR_EL2_Type := value_name
  (Mk_HDFGWTR_EL2_Type (tmp &&& (Complement.complement 0x8DFC89C440400240#64)))

def __get_CNTPS_TVAL_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTPS_TVAL_EL1_Type := value_name
  (Mk_CNTPS_TVAL_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_ICV_AP1R_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_AP1R_EL1_Type := value_name
  (Mk_ICV_AP1R_EL1_Type (tmp &&& (Complement.complement 0x7FFFFFFF00000000#64)))

def __get_LOREA_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : LOREA_EL1_Type := value_name
  (Mk_LOREA_EL1_Type (tmp &&& (Complement.complement 0xFF0000000000FFFF#64)))

def __get_CNTV_TVAL_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTV_TVAL_EL0_Type := value_name
  (Mk_CNTV_TVAL_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_ICC_IAR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICC_IAR1_EL1_Type := value_name
  (Mk_ICC_IAR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_MPIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPIDR_EL1_Type := value_name
  (Mk_MPIDR_EL1_Type ((tmp &&& (Complement.complement 0xFFFFFF003E000000#64)) ||| (Sail.BitVec.zeroExtend 0x80000000#32 64)))

def __get_DBGCLAIMCLR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGCLAIMCLR_EL1_Type := value_name
  (Mk_DBGCLAIMCLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF00#64)))

def __get_DBGWVR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGWVR_EL1_Type := value_name
  (Mk_DBGWVR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x3#4 64))))

def __get_ICV_HPPIR1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ICV_HPPIR1_EL1_Type := value_name
  (Mk_ICV_HPPIR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF000000#64)))

def __get_CNTHV_CTL_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : CNTHV_CTL_EL2_Type := value_name
  (Mk_CNTHV_CTL_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF8#64)))

def __get_ID_AA64ZFR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64ZFR0_EL1_Type := value_name
  (Mk_ID_AA64ZFR0_EL1_Type (tmp &&& (Complement.complement 0xF00F00F0F000FF00#64)))

def __get_DBGDRAR (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DBGDRAR_Type := value_name
  (Mk_DBGDRAR_Type (tmp &&& (Complement.complement 0xFF00000000000FFC#64)))

def __get_ZCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ZCR_EL3_Type := value_name
  (Mk_ZCR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_ZCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ZCR_EL1_Type := value_name
  (Mk_ZCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_ZCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ZCR_EL2_Type := value_name
  (Mk_ZCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_SMCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SMCR_EL3_Type := value_name
  (Mk_SMCR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFF3FFFFFF0#64)))

def __get_SMCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SMCR_EL1_Type := value_name
  (Mk_SMCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF3FFFFFF0#64)))

def __get_SMCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SMCR_EL2_Type := value_name
  (Mk_SMCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF3FFFFFF0#64)))

def __get_ID_AA64SMFR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64SMFR0_EL1_Type := value_name
  (Mk_ID_AA64SMFR0_EL1_Type (tmp &&& (Complement.complement 0x700E0300FFFFFFFF#64)))

def __get_MPAMHCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAMHCR_EL2_Type := value_name
  (Mk_MPAMHCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF7FFFFEFC#64)))

def __get_MPAMIDR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : MPAMIDR_EL1_Type := value_name
  let tmp : MPAMIDR_EL1_Type := (Mk_MPAMIDR_EL1_Type (tmp &&& (Complement.complement 0xC1FFFF00FFE10000#64)))
  if ((! ((_get_MPAMIDR_EL1_Type_HAS_HCR (← readReg MPAMIDR_EL1)) == 1#1)) : Bool)
  then (pure (Mk_MPAMIDR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1C0000#24 64)))))
  else (pure tmp)

def __get_MPAM2_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAM2_EL2_Type := value_name
  (Mk_MPAM2_EL2_Type (tmp &&& (Complement.complement 0x7A38000000000000#64)))

def __get_MPAM3_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAM3_EL3_Type := value_name
  (Mk_MPAM3_EL3_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xC6F000000000000#60 64))))

def __get_MPAM0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAM0_EL1_Type := value_name
  (Mk_MPAM0_EL1_Type (tmp &&& (Complement.complement 0xFFFF000000000000#64)))

def __get_MPAMSM_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAMSM_EL1_Type := value_name
  (Mk_MPAMSM_EL1_Type (tmp &&& (Complement.complement 0xFFFF00FF0000FFFF#64)))

def __get_MPAM1_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAM1_EL1_Type := value_name
  (Mk_MPAM1_EL1_Type (tmp &&& (Complement.complement 0x6FBF000000000000#64)))

def __get_MPAMVPMV_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : MPAMVPMV_EL2_Type := value_name
  (Mk_MPAMVPMV_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_GMID_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GMID_EL1_Type := value_name
  (Mk_GMID_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_TFSR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TFSR_EL3_Type := value_name
  (Mk_TFSR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))

def __get_TFSRE0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TFSRE0_EL1_Type := value_name
  (Mk_TFSRE0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))

def __get_TFSR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TFSR_EL2_Type := value_name
  (Mk_TFSR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))

def __get_TFSR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : TFSR_EL1_Type := value_name
  (Mk_TFSR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFC#64)))

def __get_RGSR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : RGSR_EL1_Type := value_name
  (Mk_RGSR_EL1_Type (tmp &&& (Complement.complement 0xFF000000000000F0#64)))

def __get_GCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCR_EL1_Type := value_name
  (Mk_GCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFE0000#64)))

def __get_AMCR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCR_EL0_Type := value_name
  (Mk_AMCR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFDFBFF#64)))

def __get_AMCNTENSET0_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCNTENSET0_EL0_Type := value_name
  (Mk_AMCNTENSET0_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_AMCNTENCLR0_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCNTENCLR0_EL0_Type := value_name
  (Mk_AMCNTENCLR0_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFF0#64)))

def __get_AMEVTYPER0_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMEVTYPER0_EL0_Type := value_name
  (Mk_AMEVTYPER0_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_AMCNTENSET1_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCNTENSET1_EL0_Type := value_name
  (Mk_AMCNTENSET1_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_AMCNTENCLR1_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCNTENCLR1_EL0_Type := value_name
  (Mk_AMCNTENCLR1_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_AMCFGR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCFGR_EL0_Type := value_name
  (Mk_AMCFGR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF0EFFC000#64)))

def __get_AMUSERENR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMUSERENR_EL0_Type := value_name
  (Mk_AMUSERENR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))

def __get_AMCG1IDR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCG1IDR_EL0_Type := value_name
  (Mk_AMCG1IDR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFF00000000#64)))

def __get_AMEVTYPER1_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMEVTYPER1_EL0_Type := value_name
  (Mk_AMEVTYPER1_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_AMCGCR_EL0 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : AMCGCR_EL0_Type := value_name
  (Mk_AMCGCR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_PMSFCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSFCR_EL1_Type := value_name
  (Mk_PMSFCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFF8FFE0#64)))

def __get_PMSIRR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSIRR_EL1_Type := value_name
  (Mk_PMSIRR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF000000FE#64)))

def __get_PMSICR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSICR_EL1_Type := value_name
  (Mk_PMSICR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xFFFFFF00000000#56 64))))

def __get_PMSDSFR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : PMSDSFR_EL1_Type := value_name
  if ((! (← (__IMPDEF_boolean "filtering on Data Source [m] is supported"))) : Bool)
  then (pure (Mk_PMSDSFR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFF#64))))
  else (pure tmp)

def __get_PMSEVFR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : PMSEVFR_EL1_Type := value_name
  let tmp : PMSEVFR_EL1_Type := (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xFFFF00000001#48 64))))
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <||> (do
           (__IMPDEF_boolean "filtering on event 2 is optionally supported"))))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x4#4 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <||> (do
           (__IMPDEF_boolean "filtering on event 4 is optionally supported"))))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x10#8 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (IsFeatureImplemented FEAT_SPEv1p2))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x40#8 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <||> (do
           (__IMPDEF_boolean "filtering on event 8 is optionally supported")) <&&> (do
           (__IMPDEF_boolean "event 8 is implemented"))))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x100#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <||> (do
           (__IMPDEF_boolean "filtering on event 9 is optionally supported")) <&&> (do
           (__IMPDEF_boolean "event 9 is implemented"))))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x200#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <||> (do
           (__IMPDEF_boolean "filtering on event 10 is optionally supported")) <&&> (do
           (__IMPDEF_boolean "event 10 is implemented"))))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x400#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (IsFeatureImplemented FEAT_SPEv1p1))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x800#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (IsFeatureImplemented FEAT_TME))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x10000#20 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p1) <&&> (do
           (IsFeatureImplemented FEAT_SVE))))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x60000#20 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <&&> (do
           (__IMPDEF_boolean "event 19 is implemented"))))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x80000#20 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <&&> (do
           (__IMPDEF_boolean "event 20 is implemented"))))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x100000#24 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <&&> (do
           (__IMPDEF_boolean "event 21 is implemented"))))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x200000#24 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <&&> (do
           (__IMPDEF_boolean "event 22 is implemented"))))) : Bool)
    then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x400000#24 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <&&> (do
         (__IMPDEF_boolean "event 23 is implemented"))))) : Bool)
  then (pure (Mk_PMSEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x800000#24 64)))))
  else (pure tmp)

def __get_PMBLIMITR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMBLIMITR_EL1_Type := value_name
  (Mk_PMBLIMITR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xFD8#12 64))))

def __get_PMBSR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMBSR_EL1_Type := value_name
  (Mk_PMBSR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFF1F03F00000#64)))

def __get_PMSCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSCR_EL2_Type := value_name
  (Mk_PMSCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF04#64)))

def __get_PMSCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSCR_EL1_Type := value_name
  (Mk_PMSCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFF04#64)))

def __get_PMSIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSIDR_EL1_Type := value_name
  (Mk_PMSIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFC000000#64)))

def __get_PMSNEVFR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : PMSNEVFR_EL1_Type := value_name
  let tmp : PMSNEVFR_EL1_Type := (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xFFFF00000001#48 64))))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "the PE supports sampling of speculative instructions"))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x2#4 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <||> (do
           (__IMPDEF_boolean "filtering on event 2 is optionally supported"))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x4#4 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <||> (do
           (__IMPDEF_boolean "filtering on event 4 is optionally supported"))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x10#8 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <||> (do
           (__IMPDEF_boolean "filtering on event 8 is optionally supported")) <&&> (do
           (__IMPDEF_boolean "event 8 is implemented"))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x100#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <||> (do
           (__IMPDEF_boolean "filtering on event 9 is optionally supported")) <&&> (do
           (__IMPDEF_boolean "event 9 is implemented"))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x200#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <||> (do
           (__IMPDEF_boolean "filtering on event 10 is optionally supported")) <&&> (do
           (__IMPDEF_boolean "event 10 is implemented"))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x400#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (IsFeatureImplemented FEAT_SPEv1p1))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x800#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 12 is not implemented, or filtering on event 12 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1000#16 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 13 is not implemented, or filtering on event 13 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x2000#16 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 14 is not implemented, or filtering on event 14 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x4000#16 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 15 is not implemented, or filtering on event 15 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x8000#16 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (IsFeatureImplemented FEAT_TME))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x10000#20 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SVE) <&&> (do
           (IsFeatureImplemented FEAT_SPEv1p1))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x60000#20 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <&&> (do
           (__IMPDEF_boolean "event 19 is implemented"))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x80000#20 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <&&> (do
           (__IMPDEF_boolean "event 20 is implemented"))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x100000#24 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <&&> (do
           (__IMPDEF_boolean "event 21 is implemented"))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x200000#24 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <&&> (do
           (__IMPDEF_boolean "event 22 is implemented"))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x400000#24 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (←((IsFeatureImplemented FEAT_SPEv1p4) <&&> (do
           (__IMPDEF_boolean "event 23 is implemented"))))) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x800000#24 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 24 is not implemented, or filtering on event 24 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1000000#28 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 25 is not implemented, or filtering on event 25 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x2000000#28 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 26 is not implemented, or filtering on event 26 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x4000000#28 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 27 is not implemented, or filtering on event 27 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x8000000#28 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 28 is not implemented, or filtering on event 28 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x10000000#32 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 29 is not implemented, or filtering on event 29 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x20000000#32 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 30 is not implemented, or filtering on event 30 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x40000000#32 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 31 is not implemented, or filtering on event 31 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x80000000#32 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 48 is not implemented, or filtering on event 48 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1000000000000#52 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 49 is not implemented, or filtering on event 49 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x2000000000000#52 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 50 is not implemented, or filtering on event 50 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x4000000000000#52 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 51 is not implemented, or filtering on event 51 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x8000000000000#52 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 52 is not implemented, or filtering on event 52 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x10000000000000#56 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 53 is not implemented, or filtering on event 53 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x20000000000000#56 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 54 is not implemented, or filtering on event 54 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x40000000000000#56 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 55 is not implemented, or filtering on event 55 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x80000000000000#56 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 56 is not implemented, or filtering on event 56 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x100000000000000#60 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 57 is not implemented, or filtering on event 57 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x200000000000000#60 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 58 is not implemented, or filtering on event 58 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x400000000000000#60 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 59 is not implemented, or filtering on event 59 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x800000000000000#60 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 60 is not implemented, or filtering on event 60 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement 0x1000000000000000#64))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 61 is not implemented, or filtering on event 61 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement 0x2000000000000000#64))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((← (__IMPDEF_boolean "event 62 is not implemented, or filtering on event 62 is not supported")) : Bool)
    then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement 0x4000000000000000#64))))
    else (pure tmp) ) : SailM (BitVec 64) )
  if ((← (__IMPDEF_boolean "event 63 is not implemented, or filtering on event 63 is not supported")) : Bool)
  then (pure (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement 0x8000000000000000#64))))
  else (pure tmp)

def __get_PMBIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMBIDR_EL1_Type := value_name
  (Mk_PMBIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFF0C0#64)))

def __get_PMSLATFR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : PMSLATFR_EL1_Type := value_name
  (Mk_PMSLATFR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_VDISR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VDISR_EL2_Type := value_name
  (Mk_VDISR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFF7E000000#64)))

def __get_ERRIDR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ERRIDR_EL1_Type := value_name
  (Mk_ERRIDR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_DISR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : DISR_EL1_Type := value_name
  (Mk_DISR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFF7E000000#64)))

def __get_ERRSELR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ERRSELR_EL1_Type := value_name
  (Mk_ERRSELR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_VSESR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VSESR_EL2_Type := value_name
  (Mk_VSESR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFE000000#64)))

def __get_BRBINF_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBINF_EL1_Type := value_name
  (Mk_BRBINF_EL1_Type (tmp &&& (Complement.complement 0xFFFF8000FFFCC01C#64)))

def __get_BRBCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBCR_EL2_Type := value_name
  (Mk_BRBCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF3FFC84#64)))

def __get_BRBFCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBFCR_EL1_Type := value_name
  (Mk_BRBFCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFCF80FF3F#64)))

def __get_BRBINFINJ_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBINFINJ_EL1_Type := value_name
  (Mk_BRBINFINJ_EL1_Type (tmp &&& (Complement.complement 0xFFFF8000FFFCC01C#64)))

def __get_BRBCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBCR_EL1_Type := value_name
  (Mk_BRBCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF3FFC84#64)))

def __get_BRBIDR0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : BRBIDR0_EL1_Type := value_name
  (Mk_BRBIDR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFF0000#64)))

def __get_GCSCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSCR_EL3_Type := value_name
  (Mk_GCSCR_EL3_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFC9E#64)))

def __get_GCSCR_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSCR_EL1_Type := value_name
  (Mk_GCSCR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFC9E#64)))

def __get_GCSCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSCR_EL2_Type := value_name
  (Mk_GCSCR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFC9E#64)))

def __get_GCSCRE0_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : GCSCRE0_EL1_Type := value_name
  (Mk_GCSCRE0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFF8DE#64)))

def __get_DBGOSDLR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : DBGOSDLR_Type := value_name
  let tmp ← (( do
    if ((! (← (IsFeatureImplemented FEAT_DoubleLock))) : Bool)
    then (pure (Mk_DBGOSDLR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1#4 32)))))
    else (pure tmp) ) : SailM (BitVec 32) )
  (pure (Mk_DBGOSDLR_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32))))

def __get_ICH_ELRSR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_ELRSR_Type := value_name
  (Mk_ICH_ELRSR_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))

def __get_ICC_IAR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IAR1_Type := value_name
  (Mk_ICC_IAR1_Type (tmp &&& (Complement.complement 0xFF000000#32)))

def __get_HCPTR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : HCPTR_Type := value_name
  let tmp : HCPTR_Type := (Mk_HCPTR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xCCC4000#28 32))))
  if ((←((pure (HaveEL EL3)) <&&> (do
       (ELUsingAArch32 EL3)) <&&> (do
       (pure (! (← (IsCurrentSecurityState SS_Secure))))) <&&> (do
       (pure ((_get_NSACR_Type_cp10 (← readReg NSACR)) == 0#1))))) : Bool)
  then (pure (Mk_HCPTR_Type ((tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x0#4 32))) ||| (Sail.BitVec.zeroExtend 0xC00#12 32))))
  else (pure tmp)

def __get_ICV_IGRPEN1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_IGRPEN1_Type := value_name
  (Mk_ICV_IGRPEN1_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))

def __get_CTR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CTR_Type := value_name
  (Mk_CTR_Type ((tmp &&& (Complement.complement 0x40003FF0#32)) ||| 0x80000000#32))

def __get_PMUSERENR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : PMUSERENR_Type := value_name
  (Mk_PMUSERENR_Type (tmp &&& (Complement.complement 0xFFFFFF80#32)))

def __get_DBGAUTHSTATUS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGAUTHSTATUS_Type := value_name
  (Mk_DBGAUTHSTATUS_Type (tmp &&& (Complement.complement 0xF0FF0F00#32)))

def __get_ICC_IAR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IAR0_Type := value_name
  (Mk_ICC_IAR0_Type (tmp &&& (Complement.complement 0xFF000000#32)))

def __get_ICV_IGRPEN0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_IGRPEN0_Type := value_name
  (Mk_ICV_IGRPEN0_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))

def __get_ICV_CTLR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_CTLR_Type := value_name
  (Mk_ICV_CTLR_Type (tmp &&& (Complement.complement 0xFFF300FC#32)))

def __get_DBGCLAIMCLR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGCLAIMCLR_Type := value_name
  (Mk_DBGCLAIMCLR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))

def __get_DBGWVR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGWVR_Type := value_name
  (Mk_DBGWVR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x3#4 32))))

def __get_ICV_HPPIR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_HPPIR1_Type := value_name
  (Mk_ICV_HPPIR1_Type (tmp &&& (Complement.complement 0xFF000000#32)))

def __get_HRMR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HRMR_Type := value_name
  (Mk_HRMR_Type (tmp &&& (Complement.complement 0xFFFFFFFC#32)))

def __get_ICH_VTR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_VTR_Type := value_name
  (Mk_ICH_VTR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x3FFE0#20 32))))

def __get_CSSELR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CSSELR_Type := value_name
  (Mk_CSSELR_Type (tmp &&& (Complement.complement 0xFFFFFFE0#32)))

def __get_CSSELR_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CSSELR_Type := value_name
  (Mk_CSSELR_Type (tmp &&& (Complement.complement 0xFFFFFFE0#32)))

def __get_CSSELR_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CSSELR_Type := value_name
  (Mk_CSSELR_Type (tmp &&& (Complement.complement 0xFFFFFFE0#32)))

def __get_PMCR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : PMCR_Type := value_name
  let tmp : PMCR_Type := (Mk_PMCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x506#12 32))))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "the implementation includes a PMU event export bus"))) : Bool)
    then (pure (Mk_PMCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x10#8 32)))))
    else (pure tmp) ) : SailM (BitVec 32) )
  if ((! (! (← (IsFeatureImplemented FEAT_PMUv3p7)))) : Bool)
  then (pure (Mk_PMCR_Type (tmp &&& (Complement.complement 0xFF000000#32))))
  else (pure tmp)

def __get_DBGWCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGWCR_Type := value_name
  (Mk_DBGWCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xE00000#24 32))))

def __get_ICH_VMCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_VMCR_Type := value_name
  (Mk_ICH_VMCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x3FDE0#20 32))))

def __get_DBGDEVID1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDEVID1_Type := value_name
  (Mk_DBGDEVID1_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))

def __get_ICC_BPR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_BPR1_Type := value_name
  (Mk_ICC_BPR1_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_ICC_BPR1_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_BPR1_Type := value_name
  (Mk_ICC_BPR1_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_ICC_BPR1_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_BPR1_Type := value_name
  (Mk_ICC_BPR1_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_ICV_RPR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_RPR_Type := value_name
  (Mk_ICV_RPR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))

def __get_ICV_IAR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_IAR1_Type := value_name
  (Mk_ICV_IAR1_Type (tmp &&& (Complement.complement 0xFF000000#32)))

def __get_DBGPRCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGPRCR_Type := value_name
  (Mk_DBGPRCR_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))

def __get_SDER (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : SDER_Type := value_name
  (Mk_SDER_Type (tmp &&& (Complement.complement 0xFFFFFFFC#32)))

def __get_ICC_BPR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_BPR0_Type := value_name
  (Mk_ICC_BPR0_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_CNTHCTL (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTHCTL_Type := value_name
  (Mk_CNTHCTL_Type (tmp &&& (Complement.complement 0xFFF00000#32)))

def __get_DBGVCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGVCR_Type := value_name
  (Mk_DBGVCR_Type (tmp &&& (Complement.complement 0x21FF2321#32)))

def __get_ICV_BPR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_BPR1_Type := value_name
  (Mk_ICV_BPR1_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_ICC_RPR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_RPR_Type := value_name
  (Mk_ICC_RPR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))

def __get_ICC_MSRE (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_MSRE_Type := value_name
  (Mk_ICC_MSRE_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))

def __get_PMMIR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : PMMIR_Type := value_name
  (Mk_PMMIR_Type (tmp &&& (Complement.complement 0xF0000000#32)))

def __get_VMPIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VMPIDR_Type := value_name
  (Mk_VMPIDR_Type ((tmp &&& (Complement.complement 0x3E000000#32)) ||| 0x80000000#32))

def __get_ICC_IGRPEN1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IGRPEN1_Type := value_name
  (Mk_ICC_IGRPEN1_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))

def __get_ICC_IGRPEN1_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IGRPEN1_Type := value_name
  (Mk_ICC_IGRPEN1_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))

def __get_ICC_IGRPEN1_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IGRPEN1_Type := value_name
  (Mk_ICC_IGRPEN1_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))

def __get_HSTR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HSTR_Type := value_name
  (Mk_HSTR_Type (tmp &&& (Complement.complement 0xFFFF4010#32)))

def __get_ICC_MCTLR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_MCTLR_Type := value_name
  (Mk_ICC_MCTLR_Type (tmp &&& (Complement.complement 0xFFF10080#32)))

def __get_PMSELR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : PMSELR_Type := value_name
  (Mk_PMSELR_Type (tmp &&& (Complement.complement 0xFFFFFFE0#32)))

def __get_DBGCLAIMSET (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGCLAIMSET_Type := value_name
  (Mk_DBGCLAIMSET_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))

def __get_ICC_IGRPEN0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_IGRPEN0_Type := value_name
  (Mk_ICC_IGRPEN0_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))

def __get_ICC_CTLR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_CTLR_Type := value_name
  (Mk_ICC_CTLR_Type (tmp &&& (Complement.complement 0xFFF300BC#32)))

def __get_ICC_CTLR_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_CTLR_Type := value_name
  (Mk_ICC_CTLR_Type (tmp &&& (Complement.complement 0xFFF300BC#32)))

def __get_ICC_CTLR_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_CTLR_Type := value_name
  (Mk_ICC_CTLR_Type (tmp &&& (Complement.complement 0xFFF300BC#32)))

def __get_SCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : SCR_Type := value_name
  (Mk_SCR_Type (tmp &&& (Complement.complement 0xFFFF4C00#32)))

def __get_NSACR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : NSACR_Type := value_name
  (Mk_NSACR_Type (tmp &&& (Complement.complement 0xFFE873FF#32)))

def __get_ICV_BPR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_BPR0_Type := value_name
  (Mk_ICV_BPR0_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_ICH_EISR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_EISR_Type := value_name
  (Mk_ICH_EISR_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))

def __get_HDCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HDCR_Type := value_name
  (Mk_HDCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x3750000#28 32))))

def __get_ICC_HSRE (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_HSRE_Type := value_name
  (Mk_ICC_HSRE_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))

def __get_PMCCFILTR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : PMCCFILTR_Type := value_name
  (Mk_PMCCFILTR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x20FFFFF#28 32))))

def __get_HTCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HTCR_Type := value_name
  (Mk_HTCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x40#8 32))))

def __get_ICC_PMR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_PMR_Type := value_name
  (Mk_ICC_PMR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))

def __get_ICH_HCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_HCR_Type := value_name
  (Mk_ICH_HCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x7FF0200#28 32))))

def __get_RMR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : RMR_Type := value_name
  (Mk_RMR_Type (tmp &&& (Complement.complement 0xFFFFFFFC#32)))

def __get_ICC_HPPIR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_HPPIR0_Type := value_name
  (Mk_ICC_HPPIR0_Type (tmp &&& (Complement.complement 0xFF000000#32)))

def __get_TTBCR2 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : TTBCR2_Type := value_name
  (Mk_TTBCR2_Type (tmp &&& (Complement.complement 0xC0000008#32)))

def __get_TTBCR2_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : TTBCR2_Type := value_name
  (Mk_TTBCR2_Type (tmp &&& (Complement.complement 0xC0000008#32)))

def __get_TTBCR2_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : TTBCR2_Type := value_name
  (Mk_TTBCR2_Type (tmp &&& (Complement.complement 0xC0000008#32)))

def __get_CNTKCTL (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTKCTL_Type := value_name
  (Mk_CNTKCTL_Type (tmp &&& (Complement.complement 0xFFFDFC00#32)))

def __get_ICV_PMR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_PMR_Type := value_name
  (Mk_ICV_PMR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))

def __get_ICV_HPPIR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_HPPIR0_Type := value_name
  (Mk_ICV_HPPIR0_Type (tmp &&& (Complement.complement 0xFF000000#32)))

def __get_DBGBCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGBCR_Type := value_name
  (Mk_DBGBCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1E10#16 32))))

def __get_HSCTLR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : HSCTLR_Type := value_name
  let tmp : HSCTLR_Type := (Mk_HSCTLR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x20200#20 32))))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_CP15BEN"))) : Bool)
    then (pure (Mk_HSCTLR_Type ((tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x0#4 32))) ||| (Sail.BitVec.zeroExtend 0x20#8 32))))
    else (pure tmp) ) : SailM (BitVec 32) )
  if ((! (← (__IMPDEF_boolean "IMPLEMENTED_ITD"))) : Bool)
  then (pure (Mk_HSCTLR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x80#8 32)))))
  else (pure tmp)

def __get_VTCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VTCR_Type := value_name
  (Mk_VTCR_Type ((tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1900000#28 32))) ||| 0x80000000#32))

def __get_ICC_MGRPEN1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_MGRPEN1_Type := value_name
  (Mk_ICC_MGRPEN1_Type (tmp &&& (Complement.complement 0xFFFFFFFC#32)))

def __get_CCSIDR2 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CCSIDR2_Type := value_name
  (Mk_CCSIDR2_Type (tmp &&& (Complement.complement 0xFF000000#32)))

def __get_ICH_MISR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_MISR_Type := value_name
  (Mk_ICH_MISR_Type (tmp &&& (Complement.complement 0xFFFFFF00#32)))

def __get_CPACR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : CPACR_Type := value_name
  let tmp : CPACR_Type := (Mk_CPACR_Type (tmp &&& (Complement.complement 0x4C0CFFFF#32)))
  if ((←((pure (HaveEL EL3)) <&&> (do
       (ELUsingAArch32 EL3)) <&&> (do
       (pure (! (← (IsCurrentSecurityState SS_Secure))))) <&&> (do
       (pure ((_get_NSACR_Type_cp10 (← readReg NSACR)) == 0#1))))) : Bool)
  then (pure (Mk_CPACR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xF00000#24 32)))))
  else (pure tmp)

def __get_ICV_IAR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICV_IAR0_Type := value_name
  (Mk_ICV_IAR0_Type (tmp &&& (Complement.complement 0xFF000000#32)))

def __get_ISR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ISR_Type := value_name
  (Mk_ISR_Type (tmp &&& (Complement.complement 0xFFFFF83F#32)))

def __get_SCTLR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : SCTLR_Type := value_name
  let tmp : SCTLR_Type := (Mk_SCTLR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x20000#20 32))))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_CP15BEN"))) : Bool)
    then (pure (Mk_SCTLR_Type ((tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x0#4 32))) ||| (Sail.BitVec.zeroExtend 0x20#8 32))))
    else (pure tmp) ) : SailM (BitVec 32) )
  if ((! (← (__IMPDEF_boolean "IMPLEMENTED_ITD"))) : Bool)
  then (pure (Mk_SCTLR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x80#8 32)))))
  else (pure tmp)

def __get_SCTLR_NS (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : SCTLR_Type := value_name
  let tmp : SCTLR_Type := (Mk_SCTLR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x20000#20 32))))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_CP15BEN"))) : Bool)
    then (pure (Mk_SCTLR_Type ((tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x0#4 32))) ||| (Sail.BitVec.zeroExtend 0x20#8 32))))
    else (pure tmp) ) : SailM (BitVec 32) )
  if ((! (← (__IMPDEF_boolean "IMPLEMENTED_ITD"))) : Bool)
  then (pure (Mk_SCTLR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x80#8 32)))))
  else (pure tmp)

def __get_SCTLR_S (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : SCTLR_Type := value_name
  let tmp : SCTLR_Type := (Mk_SCTLR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x20000#20 32))))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_CP15BEN"))) : Bool)
    then (pure (Mk_SCTLR_Type ((tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x0#4 32))) ||| (Sail.BitVec.zeroExtend 0x20#8 32))))
    else (pure tmp) ) : SailM (BitVec 32) )
  if ((! (← (__IMPDEF_boolean "IMPLEMENTED_ITD"))) : Bool)
  then (pure (Mk_SCTLR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x80#8 32)))))
  else (pure tmp)

def __get_DBGDCCINT (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDCCINT_Type := value_name
  (Mk_DBGDCCINT_Type (tmp &&& (Complement.complement 0x9FFFFFFF#32)))

def __get_DBGDSCRext (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDSCRext_Type := value_name
  (Mk_DBGDSCRext_Type (tmp &&& (Complement.complement 0x13100F82#32)))

def __get_DBGDIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGDIDR_Type := value_name
  (Mk_DBGDIDR_Type ((tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x2FFF#16 32))) ||| (Sail.BitVec.zeroExtend 0x8000#16 32)))

def __get_CNTP_CTL (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTP_CTL_Type := value_name
  (Mk_CNTP_CTL_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_CNTP_CTL_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTP_CTL_Type := value_name
  (Mk_CNTP_CTL_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_CNTP_CTL_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTP_CTL_Type := value_name
  (Mk_CNTP_CTL_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_HTRFCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : HTRFCR_Type := value_name
  (Mk_HTRFCR_Type (tmp &&& (Complement.complement 0xFFFFFF94#32)))

def __get_PMEVTYPER (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : PMEVTYPER_Type := value_name
  (Mk_PMEVTYPER_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xF0000#20 32))))

def __get_CNTV_CTL (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTV_CTL_Type := value_name
  (Mk_CNTV_CTL_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_DBGOSLSR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DBGOSLSR_Type := value_name
  (Mk_DBGOSLSR_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))

def __get_TRFCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : TRFCR_Type := value_name
  (Mk_TRFCR_Type (tmp &&& (Complement.complement 0xFFFFFF9C#32)))

def __get_CNTHP_CTL (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : CNTHP_CTL_Type := value_name
  (Mk_CNTHP_CTL_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_MPIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : MPIDR_Type := value_name
  (Mk_MPIDR_Type ((tmp &&& (Complement.complement 0x3E000000#32)) ||| 0x80000000#32))

def __get_ICH_LRC (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICH_LRC_Type := value_name
  (Mk_ICH_LRC_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x700E000#28 32))))

def __get_ICC_HPPIR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_HPPIR1_Type := value_name
  (Mk_ICC_HPPIR1_Type (tmp &&& (Complement.complement 0xFF000000#32)))

def __get_ICC_SRE (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_SRE_Type := value_name
  (Mk_ICC_SRE_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_ICC_SRE_NS (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_SRE_Type := value_name
  (Mk_ICC_SRE_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_ICC_SRE_S (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ICC_SRE_Type := value_name
  (Mk_ICC_SRE_Type (tmp &&& (Complement.complement 0xFFFFFFF8#32)))

def __get_SDCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : SDCR_Type := value_name
  (Mk_SDCR_Type (tmp &&& (Complement.complement 0xE7413FFF#32)))

def __get_AMEVTYPER0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMEVTYPER0_Type := value_name
  (Mk_AMEVTYPER0_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))

def __get_AMUSERENR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMUSERENR_Type := value_name
  (Mk_AMUSERENR_Type (tmp &&& (Complement.complement 0xFFFFFFFE#32)))

def __get_AMEVTYPER1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMEVTYPER1_Type := value_name
  (Mk_AMEVTYPER1_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))

def __get_AMCGCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCGCR_Type := value_name
  (Mk_AMCGCR_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))

def __get_AMCFGR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCFGR_Type := value_name
  (Mk_AMCFGR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0xEFFC000#28 32))))

def __get_AMCNTENCLR1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCNTENCLR1_Type := value_name
  (Mk_AMCNTENCLR1_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))

def __get_AMCNTENSET0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCNTENSET0_Type := value_name
  (Mk_AMCNTENSET0_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))

def __get_AMCNTENCLR0 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCNTENCLR0_Type := value_name
  (Mk_AMCNTENCLR0_Type (tmp &&& (Complement.complement 0xFFFFFFF0#32)))

def __get_AMCNTENSET1 (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCNTENSET1_Type := value_name
  (Mk_AMCNTENSET1_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))

def __get_AMCR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : AMCR_Type := value_name
  (Mk_AMCR_Type (tmp &&& (Complement.complement 0xFFFDFBFF#32)))

def __get_ERRIDR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ERRIDR_Type := value_name
  (Mk_ERRIDR_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))

def __get_ERRSELR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : ERRSELR_Type := value_name
  (Mk_ERRSELR_Type (tmp &&& (Complement.complement 0xFFFF0000#32)))

def __get_DISR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : DISR_Type := value_name
  (Mk_DISR_Type (tmp &&& (Complement.complement 0x7E000000#32)))

def __get_VDFSR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VDFSR_Type := value_name
  (Mk_VDFSR_Type (tmp &&& (Complement.complement 0xFE000000#32)))

def __get_VDISR (value_name : (BitVec 32)) : (BitVec 32) :=
  let tmp : VDISR_Type := value_name
  (Mk_VDISR_Type (tmp &&& (Complement.complement 0x7E000000#32)))

def __get_PAR_EL1 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : PAR_EL1_Type := value_name
  (Mk_PAR_EL1_Type (tmp &&& (Complement.complement 0xFF00000000000FFE0000000000000000#128)))

def __get_TTBR1_EL1 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : TTBR1_EL1_Type := value_name
  (Mk_TTBR1_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FFFF0000000000000000#128)))

def __get_TTBR0_EL2 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : TTBR0_EL2_Type := value_name
  (Mk_TTBR0_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FFFF0000000000000000#128)))

def __get_VTTBR_EL2 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : VTTBR_EL2_Type := value_name
  (Mk_VTTBR_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FFFF0000000000000000#128)))

def __get_TTBR0_EL1 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : TTBR0_EL1_Type := value_name
  (Mk_TTBR0_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FFFF0000000000000000#128)))

def __get_TTBR1_EL2 (value_name : (BitVec 128)) : (BitVec 128) :=
  let tmp : TTBR1_EL2_Type := value_name
  (Mk_TTBR1_EL2_Type (tmp &&& (Complement.complement 0xFFFFFFFFFF00FFFF0000000000000000#128)))

def FPSCR_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (pure ((Zeros (n := 32)) +++ (← (__get_FPSCR (← (FPSCR_read__1 ())))))) ) : SailM (BitVec 64) )
  (pure (Mk_FPCRType r))

def PC_read__1 (_ : Unit) : SailM (BitVec 32) := do
  (R_read 15)

/-- Type quantifiers: k_N : Nat, 4 < k_N -/
def DebugExceptionReturnSS (spsr : (BitVec k_N)) : SailM (BitVec 1) := do
  sail_assert (←((Halted ()) <||> (do
    (Restarting ())) <||> (do
    (pure ((← readReg PSTATE).EL != EL0))))) "src/v8_base.sail:8493.55-8493.56"
  let enabled_at_source ← (( do (undefined_bool ()) ) : SailM Bool )
  let enabled_at_source ← (( do
    if ((← (Restarting ())) : Bool)
    then (pure false)
    else
      (do
        if ((← (UsingAArch32 ())) : Bool)
        then (do (AArch32_GenerateDebugExceptions ()))
        else (do (AArch64_GenerateDebugExceptions ()))) ) : SailM Bool )
  let valid_name ← (( do (undefined_bool ()) ) : SailM Bool )
  let dest_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let dest_el ← (( do
    if ((← (IllegalExceptionReturn spsr)) : Bool)
    then (do (pure (← readReg PSTATE).EL))
    else
      (do
        let (dest_el, valid_name) ← (( do
          let (tup__0, tup__1) ← do (ELFromSPSR spsr)
          let valid_name : Bool := tup__0
          let dest_el : (BitVec 2) := tup__1
          (pure (dest_el, valid_name)) ) : SailM ((BitVec 2) × Bool) )
        sail_assert valid_name "src/v8_base.sail:8508.25-8508.26"
        (pure dest_el)) ) : SailM (BitVec 2) )
  let dest_ss ← (( do (SecurityStateAtEL dest_el) ) : SailM SecurityState )
  let mask ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let enabled_at_dest ← (( do (undefined_bool ()) ) : SailM Bool )
  let dest_using_32 ← (( do
    if ((dest_el == EL0) : Bool)
    then (pure ((BitVec.join1 [(BitVec.access spsr 4)]) == 1#1))
    else (ELUsingAArch32 dest_el) ) : SailM Bool )
  let enabled_at_dest ← (( do
    if (dest_using_32 : Bool)
    then (do (AArch32_GenerateDebugExceptionsFrom dest_el dest_ss))
    else
      (do
        sail_assert (9 <b (Sail.BitVec.length spsr)) "src/v8_base.sail:8518.33-8518.34"
        let mask : (BitVec 1) := (BitVec.join1 [(BitVec.access spsr 9)])
        (AArch64_GenerateDebugExceptionsFrom dest_el dest_ss mask)) ) : SailM Bool )
  let ELd ← (( do (DebugTargetFrom dest_ss) ) : SailM (BitVec 2) )
  let SS_bit ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  if ((((←((pure (! (← (ELUsingAArch32 ELd)))) <&&> (do
           (pure ((_get_MDSCR_EL1_Type_SS (← readReg MDSCR_EL1)) == 1#1))))) && (! enabled_at_source)) && enabled_at_dest) : Bool)
  then
    (do
      sail_assert (21 <b (Sail.BitVec.length spsr)) "src/v8_base.sail:8525.34-8525.35"
      (pure (BitVec.join1 [(BitVec.access spsr 21)])))
  else (pure 0#1)

def AArch64_WFxTrap (wfxtype : WFxType) (target_el : (BitVec 2)) : SailM Unit := do
  sail_assert ((BitVec.toNat target_el) >b (BitVec.toNat (← readReg PSTATE).EL)) "src/v8_base.sail:10642.44-10642.45"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_WFxTrap) ) : SailM ExceptionRecord )
  let except ← (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 24 20 (← (ConditionSyndrome ()))))) })
  let except ← (( do
    match wfxtype with
    | .WFxType_WFI => (pure { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 1 0 0b00#2) })
    | .WFxType_WFE => (pure { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 1 0 0b01#2) })
    | .WFxType_WFIT =>
      (do
        let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 1 0 0b10#2) }
        let except : ExceptionRecord := { except with syndrome := (BitVec.update except.syndrome 2 (Bit 1#1)) }
        (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 9 5 (Sail.BitVec.extractLsb (← (ThisInstr ())) 4 0)))) }))
    | .WFxType_WFET =>
      (do
        let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 1 0 0b11#2) }
        let except : ExceptionRecord := { except with syndrome := (BitVec.update except.syndrome 2 (Bit 1#1)) }
        (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 9 5 (Sail.BitVec.extractLsb (← (ThisInstr ())) 4 0)))) })) ) : SailM ExceptionRecord )
  if ((←((pure (target_el == EL1)) <&&> (do
       (EL2Enabled ())) <&&> (do
       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
  then (AArch64_TakeException EL2 except preferred_exception_return vect_offset)
  else (AArch64_TakeException target_el except preferred_exception_return vect_offset)

def FPProcessException (except : FPExc) (fpcr : (BitVec 64)) : SailM Unit := do
  let is_ase ← (( do (undefined_bool ()) ) : SailM Bool )
  let cumul : Nat := 0
  let cumul : Int :=
    match except with
    | .FPExc_InvalidOp => 0
    | .FPExc_DivideByZero => 1
    | .FPExc_Overflow => 2
    | .FPExc_Underflow => 3
    | .FPExc_Inexact => 4
    | .FPExc_InputDenorm => 7
  let cumul := cumul
  let enable := (cumul +i 8)
  if ((←((pure ((BitVec.join1 [(BitVec.access fpcr enable)]) == 1#1)) <&&> (do
       (pure (! (← (HaveSME ())))) <||> (do
         (pure ((← readReg PSTATE).SM == 0#1))) <||> (do
         (IsFullA64Enabled ()))))) : Bool)
  then
    (do
      let accumulated_exceptions ← (( do (GetAccumulatedFPExceptions ()) ) : SailM (BitVec 8) )
      let accumulated_exceptions : (BitVec 8) := (BitVec.update accumulated_exceptions cumul (Bit 1#1))
      if ((← (__IMPDEF_boolean "Support trapping of floating-point exceptions")) : Bool)
      then
        (do
          if ((← (UsingAArch32 ())) : Bool)
          then (AArch32_FPTrappedException accumulated_exceptions)
          else
            (do
              let is_ase ← (( do (IsASEInstruction ()) ) : SailM Bool )
              (AArch64_FPTrappedException is_ase accumulated_exceptions)))
      else (pure (SetAccumulatedFPExceptions accumulated_exceptions)))
  else
    (do
      if ((← (UsingAArch32 ())) : Bool)
      then (FPSCR_write (Mk_FPSCR_Type (Sail.BitVec.updateSubrange (← (FPSCR_read__1 ())) cumul cumul 1#1)))
      else writeReg FPSR (BitVec.update (← readReg FPSR) cumul (Bit 1#1)))

def FPRoundingMode (fpcr : (BitVec 64)) : SailM FPRounding := do
  (FPDecodeRounding (_get_FPCRType_RMode fpcr))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPDefaultNaN (N : Nat) : SailM (BitVec N) := do
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  (FPDefaultNaN__1 fpcr N)

def IsMerging (fpcr : (BitVec 64)) : SailM Bool := do
  let nep ← (( do
    if ((←((HaveSME ()) <&&> (do
         (pure ((← readReg PSTATE).SM == 1#1))) <&&> (do
         (pure (! (← (IsFullA64Enabled ()))))))) : Bool)
    then (pure 0#1)
    else (pure (_get_FPCRType_NEP fpcr)) ) : SailM (BitVec 1) )
  (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && (nep == 1#1)))

def AddPACIA (x : (BitVec 64)) (y : (BitVec 64)) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let APIAKey_EL1 ← (( do (pure ((Sail.BitVec.extractLsb (← readReg APIAKeyHi_EL1) 63 0) +++ (Sail.BitVec.extractLsb (← readReg APIAKeyLo_EL1) 63 0))) ) : SailM (BitVec 128) )
  let (Enable, TrapEL2, TrapEL3) ← (( do
    let questionMark ← do (pure (← readReg PSTATE).EL)
    let (Enable, TrapEL2, TrapEL3) ← (( do
      if ((questionMark == EL0) : Bool)
      then
        (do
          let IsEL1Regime ← (( do (pure ((← (S1TranslationRegime__1 ())) == EL1)) ) : SailM Bool )
          let Enable ←
            if (IsEL1Regime : Bool)
            then (pure (_get_SCTLR_EL1_Type_EnIA (← readReg SCTLR_EL1)))
            else (pure (_get_SCTLR_EL2_Type_EnIA (← readReg SCTLR_EL2)))
          let TrapEL2 ← (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_API (← readReg HCR_EL2)) == 0#1))) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1)) <||> (do (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))
          let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
          (pure (Enable, TrapEL2, TrapEL3)))
      else
        (do
          let (Enable, TrapEL2, TrapEL3) ← (( do
            if ((questionMark == EL1) : Bool)
            then
              (do
                let Enable ← (pure (_get_SCTLR_EL1_Type_EnIA (← readReg SCTLR_EL1)))
                let TrapEL2 ← (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_API (← readReg HCR_EL2)) == 0#1)))
                let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
                (pure (Enable, TrapEL2, TrapEL3)))
            else
              (do
                let (Enable, TrapEL2, TrapEL3) ← (( do
                  if ((questionMark == EL2) : Bool)
                  then
                    (do
                      let Enable ← (pure (_get_SCTLR_EL2_Type_EnIA (← readReg SCTLR_EL2)))
                      let TrapEL2 : Bool := false
                      let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
                      (pure (Enable, TrapEL2, TrapEL3)))
                  else
                    (do
                      let (Enable, TrapEL2, TrapEL3) ← (( do
                        if ((questionMark == EL3) : Bool)
                        then
                          (do
                            let Enable ← (pure (_get_SCTLR_EL3_Type_EnIA (← readReg SCTLR_EL3)))
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
              else (AddPAC x y APIAKey_EL1 false))))

def AddPACIB (x : (BitVec 64)) (y : (BitVec 64)) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let APIBKey_EL1 ← (( do (pure ((Sail.BitVec.extractLsb (← readReg APIBKeyHi_EL1) 63 0) +++ (Sail.BitVec.extractLsb (← readReg APIBKeyLo_EL1) 63 0))) ) : SailM (BitVec 128) )
  let (Enable, TrapEL2, TrapEL3) ← (( do
    let questionMark ← do (pure (← readReg PSTATE).EL)
    let (Enable, TrapEL2, TrapEL3) ← (( do
      if ((questionMark == EL0) : Bool)
      then
        (do
          let IsEL1Regime ← (( do (pure ((← (S1TranslationRegime__1 ())) == EL1)) ) : SailM Bool )
          let Enable ←
            if (IsEL1Regime : Bool)
            then (pure (_get_SCTLR_EL1_Type_EnIB (← readReg SCTLR_EL1)))
            else (pure (_get_SCTLR_EL2_Type_EnIB (← readReg SCTLR_EL2)))
          let TrapEL2 ← (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_API (← readReg HCR_EL2)) == 0#1))) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1)) <||> (do (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))
          let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
          (pure (Enable, TrapEL2, TrapEL3)))
      else
        (do
          let (Enable, TrapEL2, TrapEL3) ← (( do
            if ((questionMark == EL1) : Bool)
            then
              (do
                let Enable ← (pure (_get_SCTLR_EL1_Type_EnIB (← readReg SCTLR_EL1)))
                let TrapEL2 ← (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_API (← readReg HCR_EL2)) == 0#1)))
                let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
                (pure (Enable, TrapEL2, TrapEL3)))
            else
              (do
                let (Enable, TrapEL2, TrapEL3) ← (( do
                  if ((questionMark == EL2) : Bool)
                  then
                    (do
                      let Enable ← (pure (_get_SCTLR_EL2_Type_EnIB (← readReg SCTLR_EL2)))
                      let TrapEL2 : Bool := false
                      let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
                      (pure (Enable, TrapEL2, TrapEL3)))
                  else
                    (do
                      let (Enable, TrapEL2, TrapEL3) ← (( do
                        if ((questionMark == EL3) : Bool)
                        then
                          (do
                            let Enable ← (pure (_get_SCTLR_EL3_Type_EnIB (← readReg SCTLR_EL3)))
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
              else (AddPAC x y APIBKey_EL1 false))))

def AddPACDA (x : (BitVec 64)) (y : (BitVec 64)) : SailM (BitVec 64) := do
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
              else (AddPAC x y APDAKey_EL1 true))))

def AddPACDB (x : (BitVec 64)) (y : (BitVec 64)) : SailM (BitVec 64) := do
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
              else (AddPAC x y APDBKey_EL1 true))))

def AArch64_CheckSystemAccess (op0 : (BitVec 2)) (op1 : (BitVec 3)) (crn : (BitVec 4)) (crm : (BitVec 4)) (op2 : (BitVec 3)) (rt : (BitVec 5)) (read : (BitVec 1)) : SailM Unit := do
  if ((← (HaveBTIExt ())) : Bool)
  then (BranchTargetCheck ())
  else (pure ())
  if ((←((HaveTME ()) <&&> (do
       (pure ((← readReg TSTATE).depth >b 0))) <&&> (do
       (pure (! (← (CheckTransactionalSystemAccess op0 op1 crn crm op2 read))))))) : Bool)
  then (FailTransaction TMFailure_ERR false)
  else (pure ())

def AArch64_RandomTag (_ : Unit) : SailM (BitVec 4) := do
  let tag ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let loop_i_lower := 0
  let loop_i_upper := 3
  let mut loop_vars := tag
  for i in [loop_i_lower:loop_i_upper:1]i do
    let tag := loop_vars
    loop_vars ← do (pure (BitVec.update tag i (Bit (← (AArch64_NextRandomTagBit ())))))
  (pure loop_vars)

/-- Type quantifiers: k_N : Nat, k_soft : Bool, List.elem k_N [64, 128] -/
def RCWCheck (old : (BitVec k_N)) (new : (BitVec k_N)) (soft : Bool) : SailM (BitVec 4) := do
  sail_assert (((Sail.BitVec.length old) == 64) || ((Sail.BitVec.length old) == 128)) "src/v8_base.sail:28509.31-28509.32"
  let protectedbit :=
    if (((Sail.BitVec.length old) == 128) : Bool)
    then RCW128_PROTECTED_BIT
    else RCW64_PROTECTED_BIT
  let rcw_fail : Bool := false
  let rcws_fail : Bool := false
  let rcw_state_fail : Bool := false
  let rcws_state_fail : Bool := false
  let rcw_mask_fail : Bool := false
  let rcws_mask_fail : Bool := false
  let rcwmask ← (( do (pure (Sail.BitVec.extractLsb (← readReg RCWMASK_EL1) ((Sail.BitVec.length old) -i 1) 0)) ) : SailM (BitVec k_N) )
  let rcwmask : (BitVec k_N) :=
    if (((Sail.BitVec.length rcwmask) == 64) : Bool)
    then
      (let rcwmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwmask 49 18 (BitVec.replicateBits (BitVec.join1 [(BitVec.access rcwmask 17)]) 32))
      (BitVec.update rcwmask 0 (Bit 0#1)))
    else
      (let rcwmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwmask 55 17 (BitVec.replicateBits (BitVec.join1 [(BitVec.access rcwmask 16)]) 39))
      let split_vec := (Zeros (n := 48))
      let rcwmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwmask 126 125 (Sail.BitVec.extractLsb split_vec 47 46))
      let rcwmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwmask 120 119 (Sail.BitVec.extractLsb split_vec 45 44))
      let rcwmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwmask 107 101 (Sail.BitVec.extractLsb split_vec 43 37))
      let rcwmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwmask 90 56 (Sail.BitVec.extractLsb split_vec 36 2))
      (Sail.BitVec.updateSubrange rcwmask 1 0 (Sail.BitVec.extractLsb split_vec 1 0)))
  let rcwsoftmask ← (( do (pure (Sail.BitVec.extractLsb (← readReg RCWSMASK_EL1) ((Sail.BitVec.length rcwmask) -i 1) 0)) ) : SailM (BitVec k_N) )
  let rcwsoftmask ← (( do
    if (((Sail.BitVec.length rcwsoftmask) == 64) : Bool)
    then
      (do
        let rcwsoftmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwsoftmask 49 18 (BitVec.replicateBits (BitVec.join1 [(BitVec.access rcwsoftmask 17)]) 32))
        let rcwsoftmask : (BitVec k_N) := (BitVec.update rcwsoftmask 0 (Bit 0#1))
        if ((← (ProtectionEnabled (← readReg PSTATE).EL)) : Bool)
        then (pure (BitVec.update rcwsoftmask 52 (Bit 0#1)))
        else (pure rcwsoftmask))
    else
      (let rcwsoftmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwsoftmask 55 17 (BitVec.replicateBits (BitVec.join1 [(BitVec.access rcwsoftmask 16)]) 39))
      let rcwsoftmask : (BitVec k_N) :=
        let split_vec := (Zeros (n := 48))
        let rcwsoftmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwsoftmask 126 125 (Sail.BitVec.extractLsb split_vec 47 46))
        let rcwsoftmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwsoftmask 120 119 (Sail.BitVec.extractLsb split_vec 45 44))
        let rcwsoftmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwsoftmask 107 101 (Sail.BitVec.extractLsb split_vec 43 37))
        let rcwsoftmask : (BitVec k_N) := (Sail.BitVec.updateSubrange rcwsoftmask 90 56 (Sail.BitVec.extractLsb split_vec 36 2))
        (Sail.BitVec.updateSubrange rcwsoftmask 1 0 (Sail.BitVec.extractLsb split_vec 1 0))
      (pure (BitVec.update rcwsoftmask 114 (Bit 0#1)))) ) : SailM (BitVec k_N) )
  let rcw_state_fail ← (( do
    if ((← (ProtectionEnabled (← readReg PSTATE).EL)) : Bool)
    then
      (do
        sail_assert ((0 ≤b protectedbit) && (protectedbit <b (Sail.BitVec.length rcwsoftmask))) "src/v8_base.sail:28540.68-28540.69"
        if (((BitVec.join1 [(BitVec.access old protectedbit)]) == 1#1) : Bool)
        then (pure (((BitVec.join1 [(BitVec.access new protectedbit)]) +++ (BitVec.join1 [(BitVec.access new 0)])) != ((BitVec.join1 [(BitVec.access old protectedbit)]) +++ (BitVec.join1 [(BitVec.access old 0)]))))
        else
          (if (((BitVec.join1 [(BitVec.access old protectedbit)]) == 0#1) : Bool)
          then (pure ((BitVec.join1 [(BitVec.access new protectedbit)]) != (BitVec.join1 [(BitVec.access old protectedbit)])))
          else (pure rcw_state_fail)))
    else (pure rcw_state_fail) ) : SailM Bool )
  let rcw_mask_fail ← (( do
    if ((← (ProtectionEnabled (← readReg PSTATE).EL)) : Bool)
    then
      (do
        sail_assert ((0 ≤b protectedbit) && (protectedbit <b (Sail.BitVec.length rcwsoftmask))) "src/v8_base.sail:28548.68-28548.69"
        if ((((BitVec.join1 [(BitVec.access old protectedbit)]) +++ (BitVec.join1 [(BitVec.access old 0)])) == 0b11#2) : Bool)
        then (pure (! (IsZero ((new ^^^ old) &&& (Complement.complement rcwmask)))))
        else (pure rcw_mask_fail))
    else (pure rcw_mask_fail) ) : SailM Bool )
  let (rcws_mask_fail, rcws_state_fail) ← (( do
    if (soft : Bool)
    then
      (do
        let rcws_state_fail ← (( do
          if (((BitVec.join1 [(BitVec.access old 0)]) == 1#1) : Bool)
          then (pure ((BitVec.join1 [(BitVec.access new 0)]) != (BitVec.join1 [(BitVec.access old 0)])))
          else
            (do
              sail_assert ((0 ≤b protectedbit) && (protectedbit <b (Sail.BitVec.length rcwsoftmask))) "src/v8_base.sail:28558.72-28558.73"
              if ((←((pure (! (← (ProtectionEnabled (← readReg PSTATE).EL)))) <||> (do
                   (pure ((← (ProtectionEnabled (← readReg PSTATE).EL)) && ((BitVec.join1 [(BitVec.access old protectedbit)]) == 0#1)))))) : Bool)
              then (pure ((BitVec.join1 [(BitVec.access new 0)]) != (BitVec.join1 [(BitVec.access old 0)])))
              else (pure rcws_state_fail)) ) : SailM Bool )
        let rcws_mask_fail : Bool :=
          if (((BitVec.join1 [(BitVec.access old 0)]) == 1#1) : Bool)
          then (! (IsZero ((new ^^^ old) &&& (Complement.complement rcwsoftmask))))
          else rcws_mask_fail
        (pure (rcws_mask_fail, rcws_state_fail)))
    else (pure (rcws_mask_fail, rcws_state_fail)) ) : SailM (Bool × Bool) )
  let rcw_fail : Bool := (rcw_state_fail || rcw_mask_fail)
  let rcws_fail : Bool := (rcws_state_fail || rcws_mask_fail)
  let n : (BitVec 1) := 0#1
  let z : (BitVec 1) :=
    if (rcw_fail : Bool)
    then 1#1
    else 0#1
  let c : (BitVec 1) :=
    if (rcws_fail : Bool)
    then 0#1
    else 1#1
  let v : (BitVec 1) := 0#1
  (pure (((n +++ z) +++ c) +++ v))

/-- Type quantifiers: offset : Int -/
def NVMem_read (offset : Int) : SailM (BitVec 64) := do
  sail_assert (offset >b 0) "src/v8_base.sail:28757.21-28757.22"
  let size := 64
  (NVMem_read__1 offset size)

/-- Type quantifiers: offset : Int -/
def NVMem_set (offset : Int) (value_name : (BitVec 64)) : SailM Unit := do
  sail_assert (offset >b 0) "src/v8_base.sail:28776.21-28776.22"
  let size := 64
  (NVMem_set__1 offset size value_name)

def AArch64_AdvSIMDFPAccessTrap (target_el : (BitVec 2)) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  let vect_offset := (BitVec.toNat 0x0#4)
  let route_to_el2 ← (( do (pure (target_el == EL1)) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))) ) : SailM Bool )
  if (route_to_el2 : Bool)
  then
    (do
      let except ← (( do (ExceptionSyndrome Exception_Uncategorized) ) : SailM ExceptionRecord )
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else
    (do
      let except ← (( do (ExceptionSyndrome Exception_AdvSIMDFPAccessTrap) ) : SailM ExceptionRecord )
      let except ← (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 24 20 (← (ConditionSyndrome ()))))) })
      (AArch64_TakeException target_el except preferred_exception_return vect_offset))

def SetPSTATE_ZA (value_name : (BitVec 1)) : SailM Unit := do
  if (((← readReg PSTATE).ZA != value_name) : Bool)
  then
    (do
      (ResetSMEState ())
      writeReg PSTATE { (← readReg PSTATE) with ZA := value_name })
  else (pure ())

/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def AnyActiveElement (mask : (BitVec k_N)) (esize : Int) : SailM Bool := do
  (pure ((← (LastActiveElement mask esize)) ≥b 0))

/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def PredTest (mask : (BitVec k_N)) (result : (BitVec k_N)) (esize : Int) : SailM (BitVec 4) := do
  let n ← (( do (FirstActive mask result esize) ) : SailM (BitVec 1) )
  let z ← (( do (NoneActive mask result esize) ) : SailM (BitVec 1) )
  let c ← (( do (pure (Complement.complement (← (LastActive mask result esize)))) ) : SailM (BitVec 1) )
  let v : (BitVec 1) := 0#1
  (pure (((n +++ z) +++ c) +++ v))

/-- Type quantifiers: esize : Nat, slice_name : Int, tile : Int, width : Nat, width ≥ 0 ∧ esize ≥ 0 ∧ (slice_name * esize) ≤ (slice_name * esize + esize - 1) ∨ (not (slice_name ≥ 0 ∧ ((slice_name + 1) * esize) ≤ width)) -/
def ZAvslice_read (tile : Int) (esize : Nat) (slice_name : Int) (width : Nat) : SailM (BitVec width) := do
  let SVL ← do (CurrentSVL_read ())
  let slices := (fdiv_int SVL esize)
  let result ← (( do (undefined_bitvector width) ) : SailM (BitVec width) )
  let loop_s_lower := 0
  let loop_s_upper := (slices -i 1)
  let mut loop_vars := result
  for s in [loop_s_lower:loop_s_upper:1]i do
    let result := loop_vars
    loop_vars ← do
      let hslice ← (( do (ZAhslice_read tile esize s width) ) : SailM (BitVec width) )
      sail_assert (((s *i esize) ≤b (((s +i 1) *i esize) -i 1)) || (! ((s ≥b 0) && (((s +i 1) *i esize) ≤b width)))) "src/v8_base.sail:31191.132-31191.133"
      (Elem_set result s esize (← (Elem_read hslice slice_name esize)))
  (pure loop_vars)

/-- Type quantifiers: esize : Nat, slice_name : Int, tile : Int, width : Nat, width ≥ 0 ∧ esize ≥ 0 -/
def ZAvslice_set (tile : Int) (esize : Nat) (slice_name : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let SVL ← do (CurrentSVL_read ())
  let slices := (fdiv_int SVL esize)
  let loop_s_lower := 0
  let loop_s_upper := (slices -i 1)
  let mut loop_vars := ()
  for s in [loop_s_lower:loop_s_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let hslice ← (( do (ZAhslice_read tile esize s width) ) : SailM (BitVec width) )
      sail_assert (((s *i esize) ≤b (((s *i esize) +i esize) -i 1)) || (! ((s ≥b 0) && (((s +i 1) *i esize) ≤b width)))) "src/v8_base.sail:31206.135-31206.136"
      let hslice ← (Elem_set hslice slice_name esize (← (Elem_read value_name s esize)))
      (ZAhslice_set tile esize s width hslice)
  (pure loop_vars)

/-- Type quantifiers: SVL : Int, esize : Int, tile : Int, width : Nat, width ≥ 0 -/
def ZAtile_read (SVL : Int) (tile : Int) (esize : Int) (width : Nat) : SailM (BitVec width) := do
  let slices := (fdiv_int SVL esize)
  sail_assert (width == (SVL *i slices)) "src/v8_base.sail:31249.32-31249.33"
  let result ← (( do (undefined_bitvector width) ) : SailM (BitVec width) )
  let loop_slice_name_lower := 0
  let loop_slice_name_upper := (slices -i 1)
  let mut loop_vars := result
  for slice_name in [loop_slice_name_lower:loop_slice_name_upper:1]i do
    let result := loop_vars
    loop_vars ← do
      sail_assert (((slice_name *i SVL) ≤b (((slice_name +i 1) *i SVL) -i 1)) || (! ((slice_name ≥b 0) && (((slice_name +i 1) *i SVL) ≤b width)))) "src/v8_base.sail:31252.162-31252.163"
      (Elem_set result slice_name SVL (← (ZAhslice_read tile esize slice_name SVL)))
  (pure loop_vars)

/-- Type quantifiers: SVL : Int, esize : Int, tile : Int, width : Nat, width ≥ 0 -/
def ZAtile_set (SVL : Int) (tile : Int) (esize : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let slices := (fdiv_int SVL esize)
  sail_assert (width == (SVL *i slices)) "src/v8_base.sail:31264.32-31264.33"
  let loop_slice_name_lower := 0
  let loop_slice_name_upper := (slices -i 1)
  let mut loop_vars := ()
  for slice_name in [loop_slice_name_lower:loop_slice_name_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      sail_assert (((slice_name *i SVL) ≤b (((slice_name *i SVL) +i SVL) -i 1)) || (! ((slice_name ≥b 0) && (((slice_name +i 1) *i SVL) ≤b width)))) "src/v8_base.sail:31266.163-31266.164"
      (ZAhslice_set tile esize slice_name SVL (← (Elem_read value_name slice_name SVL)))
  (pure loop_vars)

def GCSPUSHX (_ : Unit) : SailM Unit := do
  let spsr ← (( do (SPSR_read (N := 64)) ) : SailM (BitVec 64) )
  if ((! (← (GCSEnabled (← readReg PSTATE).EL))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  (AddGCSExRecord (← (ELR_read__1 ())) spsr (← (X_read 30 64)))
  writeReg PSTATE { (← readReg PSTATE) with EXLOCK := 0#1 }

def GCSPOPCX (_ : Unit) : SailM Unit := do
  let spsr ← (( do (SPSR_read (N := 64)) ) : SailM (BitVec 64) )
  if ((! (← (GCSEnabled (← readReg PSTATE).EL))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  (CheckGCSExRecord (← (ELR_read__1 ())) spsr (← (X_read 30 64)) GCSInstType_POPCX)
  writeReg PSTATE { (← readReg PSTATE) with EXLOCK := ← (do 
    if ((← (GetCurrentEXLOCKEN ())) : Bool)
    then (pure 1#1)
    else (pure 0#1)) }

/-- Type quantifiers: destreg : Int, k_from_epilogue : Bool, k_option_a_name : Bool, sizereg : Int, srcreg : Int, k_wrong_option : Bool -/
def MismatchedMemCpyException (option_a_name : Bool) (destreg : Int) (srcreg : Int) (sizereg : Int) (wrong_option : Bool) (from_epilogue : Bool) (options_name : (BitVec 4)) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let target_el ← (( do (MismatchedCpySetTargetEL ()) ) : SailM (BitVec 2) )
  let except ← (( do (ExceptionSyndrome Exception_MemCpyMemSet) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := (BitVec.update except.syndrome 24 (Bit 0#1)) }
  let except : ExceptionRecord := { except with syndrome := (BitVec.update except.syndrome 23 (Bit 0#1)) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 22 19 options_name) }
  let except : ExceptionRecord :=
    { except with syndrome := 
      (BitVec.update except.syndrome 18
        (Bit
          (if (from_epilogue : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := 
      (BitVec.update except.syndrome 17
        (Bit
          (if (wrong_option : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := 
      (BitVec.update except.syndrome 16
        (Bit
          (if (option_a_name : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 14 10 (integer_subrange destreg 4 0)) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5 (integer_subrange srcreg 4 0)) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 (integer_subrange sizereg 4 0)) }
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)

/-- Type quantifiers: datareg : Int, destreg : Int, k_from_epilogue : Bool, k_is_SETG : Bool, k_option_a_name : Bool, sizereg : Int, k_wrong_option : Bool -/
def MismatchedMemSetException (option_a_name : Bool) (destreg : Int) (datareg : Int) (sizereg : Int) (wrong_option : Bool) (from_epilogue : Bool) (options_name : (BitVec 2)) (is_SETG : Bool) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let target_el ← (( do (MismatchedCpySetTargetEL ()) ) : SailM (BitVec 2) )
  let except ← (( do (ExceptionSyndrome Exception_MemCpyMemSet) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := (BitVec.update except.syndrome 24 (Bit 1#1)) }
  let except : ExceptionRecord :=
    { except with syndrome := 
      (BitVec.update except.syndrome 23
        (Bit
          (if (is_SETG : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 20 19 options_name) }
  let except : ExceptionRecord :=
    { except with syndrome := 
      (BitVec.update except.syndrome 18
        (Bit
          (if (from_epilogue : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := 
      (BitVec.update except.syndrome 17
        (Bit
          (if (wrong_option : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := 
      (BitVec.update except.syndrome 16
        (Bit
          (if (option_a_name : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 14 10 (integer_subrange destreg 4 0)) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5 (integer_subrange datareg 4 0)) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 (integer_subrange sizereg 4 0)) }
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)

/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMulH (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec (2 * k_N)) := do
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert ((Sail.BitVec.length op2) == 16) "src/v8_base.sail:32106.19-32106.20"
  let result ← (( do (undefined_bitvector (2 *i (Sail.BitVec.length op2))) ) : SailM (BitVec (2 * k_N)) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (BFUnpack op1)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (BFUnpack op2)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  if (((BEq.beq type1 FPType_QNaN) || (BEq.beq type2 FPType_QNaN)) : Bool)
  then (do (FPDefaultNaN__1 fpcr (2 *i (Sail.BitVec.length op2))))
  else
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
      then (do (FPDefaultNaN__1 fpcr (2 *i (Sail.BitVec.length op2))))
      else
        (do
          if ((inf1 || inf2) : Bool)
          then (do (FPInfinity (sign1 ^^^ sign2) (2 *i (Sail.BitVec.length op2))))
          else
            (do
              if ((zero1 || zero2) : Bool)
              then (do (FPZero (sign1 ^^^ sign2) (2 *i (Sail.BitVec.length op2))))
              else (do (BFRound (mult_real value1_name value2_name) (2 *i (Sail.BitVec.length op2)))))))

/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPAdd_BF16 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let result_value ← (( do (undefined_real ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real ()) ) : SailM real )
  let value2_name ← (( do (undefined_real ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool ()) ) : SailM Bool )
  sail_assert ((Sail.BitVec.length op2) == 32) "src/v8_base.sail:32145.19-32145.20"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let (sign1, type1, value1_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (BFUnpack op1)
    let type1 : FPType := tup__0
    let sign1 : (BitVec 1) := tup__1
    let value1_name : real := tup__2
    (pure (sign1, type1, value1_name)) ) : SailM ((BitVec 1) × FPType × real) )
  let (sign2, type2, value2_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (BFUnpack op2)
    let type2 : FPType := tup__0
    let sign2 : (BitVec 1) := tup__1
    let value2_name : real := tup__2
    (pure (sign2, type2, value2_name)) ) : SailM ((BitVec 1) × FPType × real) )
  if (((BEq.beq type1 FPType_QNaN) || (BEq.beq type2 FPType_QNaN)) : Bool)
  then (do (FPDefaultNaN__1 fpcr (Sail.BitVec.length result)))
  else
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      if (((inf1 && inf2) && (sign1 == (Complement.complement sign2))) : Bool)
      then (do (FPDefaultNaN__1 fpcr (Sail.BitVec.length result)))
      else
        (do
          if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 0#1))) : Bool)
          then (do (FPInfinity 0#1 (Sail.BitVec.length result)))
          else
            (do
              if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 1#1))) : Bool)
              then (do (FPInfinity 1#1 (Sail.BitVec.length result)))
              else
                (do
                  if (((zero1 && zero2) && (sign1 == sign2)) : Bool)
                  then (do (FPZero sign1 (Sail.BitVec.length result)))
                  else
                    (do
                      let result_value : real := (add_real value1_name value2_name)
                      if ((eq_real result_value (0)) : Bool)
                      then (do (FPZero 0#1 (Sail.BitVec.length result)))
                      else (do (BFRound result_value (Sail.BitVec.length result))))))))

def AArch64_ESBOperation (_ : Unit) : SailM Unit := do
  let implicit_esb ← (( do (undefined_bool ()) ) : SailM Bool )
  let target_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let masked ← (( do (undefined_bool ()) ) : SailM Bool )
  let (masked, target_el) ← (( do
    let (tup__0, tup__1) ← do (AArch64_PhysicalSErrorTarget ())
    let masked : Bool := tup__0
    let target_el : (BitVec 2) := tup__1
    (pure (masked, target_el)) ) : SailM (Bool × (BitVec 2)) )
  let intdis ← (( do (Halted ()) <||> (do (ExternalDebugInterruptsDisabled target_el)) ) : SailM Bool )
  let masked : Bool := (masked || intdis)
  if ((←((pure masked) <&&> (do
       (IsSynchronizablePhysicalSErrorPending ())))) : Bool)
  then
    (do
      if ((← (ELUsingAArch32 (← (S1TranslationRegime__1 ())))) : Bool)
      then
        (do
          let syndrome : (BitVec 32) := (Zeros (n := 32))
          let syndrome : (BitVec 32) := (BitVec.update syndrome 31 (Bit 1#1))
          let syndrome ← (pure (Sail.BitVec.updateSubrange syndrome 15 0 (← (AArch32_PhysicalSErrorSyndrome ()))))
          (DISR_write (Mk_DISR_Type syndrome)))
      else
        (do
          let implicit_esb : Bool := false
          let syndrome : (BitVec 64) := (Zeros (n := 64))
          let syndrome : (BitVec 64) := (BitVec.update syndrome 31 (Bit 1#1))
          let syndrome ← (pure (Sail.BitVec.updateSubrange syndrome 24 0 (← (AArch64_PhysicalSErrorSyndrome implicit_esb))))
          writeReg DISR_EL1 (Mk_DISR_EL1_Type syndrome))
      (pure (ClearPendingPhysicalSError ())))
  else (pure ())

def AArch32_IMPDEFResets (_ : Unit) : SailM Unit := do
  (PMCR_write (_update_PMCR_Type_IMP (← (PMCR_read ())) (Zeros (n := 8))))
  (PMCR_write
    (_update_PMCR_Type_IDCODE (← (PMCR_read ()))
      (← (do
        if ((IsZero (_get_PMCR_Type_IMP (← (PMCR_read ())))) : Bool)
        then (pure (Zeros (n := 8)))
        else (pure CFG_PMCR_IDCODE)))))
  (PMCR_write (_update_PMCR_Type_N (← (PMCR_read ())) (integer_subrange (← readReg NUM_PMU_COUNTERS) 4 0)))
  (PMCR_write (_update_PMCR_Type_C (← (PMCR_read ())) 0#1))
  (PMCR_write (_update_PMCR_Type_P (← (PMCR_read ())) 0#1))
  (PMCEID0_write (Mk_PMCEID0_Type 0b01001000000000100000000100000001#32))
  (PMCEID2_write (Mk_PMCEID2_Type (Sail.BitVec.zeroExtend 0b1111#4 32)))
  (PMCEID1_write (Mk_PMCEID1_Type (Zeros (n := 32))))
  (PMCEID3_write (Mk_PMCEID3_Type (Zeros (n := 32))))
  writeReg PMCFGR (Sail.BitVec.updateSubrange (← readReg PMCFGR) 31 28 0b0000#4)
  writeReg PMCFGR (Sail.BitVec.updateSubrange (← readReg PMCFGR) 21 21 1#1)
  writeReg PMCFGR (Sail.BitVec.updateSubrange (← readReg PMCFGR) 19 19 0#1)
  writeReg PMCFGR (Sail.BitVec.updateSubrange (← readReg PMCFGR) 18 18 0#1)
  writeReg PMCFGR (Sail.BitVec.updateSubrange (← readReg PMCFGR) 17 17 0#1)
  writeReg PMCFGR (Sail.BitVec.updateSubrange (← readReg PMCFGR) 16 16 0#1)
  writeReg PMCFGR (Sail.BitVec.updateSubrange (← readReg PMCFGR) 15 15 1#1)
  writeReg PMCFGR (Sail.BitVec.updateSubrange (← readReg PMCFGR) 14 14 1#1)
  writeReg PMCFGR (Sail.BitVec.updateSubrange (← readReg PMCFGR) 13 8 0b111111#6)
  writeReg PMCFGR (Sail.BitVec.updateSubrange (← readReg PMCFGR) 7 0 (0b000#3 +++ (integer_subrange (← readReg NUM_PMU_COUNTERS) 4 0)))
  writeReg PMDEVTYPE (Sail.BitVec.updateSubrange (← readReg PMDEVTYPE) 7 4 0b0001#4)
  writeReg PMDEVTYPE (Sail.BitVec.updateSubrange (← readReg PMDEVTYPE) 3 0 0b0110#4)
  writeReg PMPIDR0 (Sail.BitVec.updateSubrange (← readReg PMPIDR0) 7 0 0b00001111#8)
  writeReg PMPIDR1 (Sail.BitVec.updateSubrange (← readReg PMPIDR1) 7 4 0b1011#4)
  writeReg PMPIDR1 (Sail.BitVec.updateSubrange (← readReg PMPIDR1) 3 0 0b1101#4)
  writeReg PMPIDR2 (Sail.BitVec.updateSubrange (← readReg PMPIDR2) 7 4 0b0000#4)
  writeReg PMPIDR2 (Sail.BitVec.updateSubrange (← readReg PMPIDR2) 3 3 1#1)
  writeReg PMPIDR2 (Sail.BitVec.updateSubrange (← readReg PMPIDR2) 2 0 0b011#3)
  writeReg PMPIDR3 (Sail.BitVec.updateSubrange (← readReg PMPIDR3) 7 4 0b0000#4)
  writeReg PMPIDR3 (Sail.BitVec.updateSubrange (← readReg PMPIDR3) 3 0 0b0000#4)
  writeReg PMPIDR4 (Sail.BitVec.updateSubrange (← readReg PMPIDR4) 7 4 0b0000#4)
  writeReg PMPIDR4 (Sail.BitVec.updateSubrange (← readReg PMPIDR4) 3 0 0b0100#4)
  writeReg PMCIDR0 (Sail.BitVec.updateSubrange (← readReg PMCIDR0) 7 0 0b00001101#8)
  writeReg PMCIDR1 (Sail.BitVec.updateSubrange (← readReg PMCIDR1) 7 4 0b1001#4)
  writeReg PMCIDR1 (Sail.BitVec.updateSubrange (← readReg PMCIDR1) 3 0 0b0000#4)
  writeReg PMCIDR2 (Sail.BitVec.updateSubrange (← readReg PMCIDR2) 7 0 0b00000101#8)
  writeReg PMCIDR3 (Sail.BitVec.updateSubrange (← readReg PMCIDR3) 7 0 0b10110001#8)
  writeReg VBAR_S (Sail.BitVec.updateSubrange (← readReg VBAR_S) 31 5 (Zeros (n := 27)))
  (CCSIDR_write (_update_CCSIDR_Type_Associativity (← (CCSIDR_read ())) (Sail.BitVec.zeroExtend 0x1#4 21)))
  (CCSIDR_write (_update_CCSIDR_Type_LineSize (← (CCSIDR_read ())) 0b010#3))
  (CLIDR_write (_update_CLIDR_Type_ICB (← (CLIDR_read ())) 0b00#2))
  (CLIDR_write (_update_CLIDR_Type_LoUU (← (CLIDR_read ())) 0b000#3))
  (CLIDR_write (_update_CLIDR_Type_LoUIS (← (CLIDR_read ())) 0b000#3))
  (CLIDR_write (Mk_CLIDR_Type (Sail.BitVec.updateSubrange (← (CLIDR_read ())) 20 0 0b000000000000000100011#21)))
  (CTR_write (_update_CTR_Type_DIC (← (CTR_read ())) 0#1))
  (CTR_write (_update_CTR_Type_IDC (← (CTR_read ())) 0#1))
  (CTR_write (_update_CTR_Type_CWG (← (CTR_read ())) 0b0100#4))
  (CTR_write (_update_CTR_Type_ERG (← (CTR_read ())) (← readReg __exclusive_granule_size)))
  (CTR_write (_update_CTR_Type_DminLine (← (CTR_read ())) 0b0100#4))
  (CTR_write (_update_CTR_Type_L1Ip (← (CTR_read ())) 0b10#2))
  (CTR_write (_update_CTR_Type_IminLine (← (CTR_read ())) 0b0100#4))
  writeReg FPSID (Sail.BitVec.updateSubrange (← readReg FPSID) 31 24 0b01000001#8)
  writeReg FPSID (Sail.BitVec.updateSubrange (← readReg FPSID) 23 23 0#1)
  writeReg FPSID (Sail.BitVec.updateSubrange (← readReg FPSID) 22 16 0b0000100#7)
  writeReg FPSID (Sail.BitVec.updateSubrange (← readReg FPSID) 15 8 0b00110000#8)
  writeReg FPSID (Sail.BitVec.updateSubrange (← readReg FPSID) 7 4 0b0111#4)
  writeReg FPSID (Sail.BitVec.updateSubrange (← readReg FPSID) 3 0 0b0000#4)
  (ID_DFR0_write (_update_ID_DFR0_Type_MProfDbg (← (ID_DFR0_read ())) 0b0000#4))
  (ID_DFR0_write (_update_ID_DFR0_Type_MMapDbg (← (ID_DFR0_read ())) 0b0000#4))
  if ((←((pure (! (HaveEL EL3))) <&&> (do
       (pure ((_get_SCR_Type_NS (← readReg SCR)) == 1#1))))) : Bool)
  then (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg (← (ID_DFR0_read ())) 0b0000#4))
  else (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg (← (ID_DFR0_read ())) (_get_ID_DFR0_Type_CopDbg (← (ID_DFR0_read ())))))
  (ID_ISAR0_write (_update_ID_ISAR0_Type_Divide (← (ID_ISAR0_read ())) 0b0010#4))
  (ID_ISAR0_write (_update_ID_ISAR0_Type_Debug (← (ID_ISAR0_read ())) 0b0001#4))
  (ID_ISAR0_write (_update_ID_ISAR0_Type_Coproc (← (ID_ISAR0_read ())) 0b0000#4))
  (ID_ISAR0_write (_update_ID_ISAR0_Type_CmpBranch (← (ID_ISAR0_read ())) 0b0001#4))
  (ID_ISAR0_write (_update_ID_ISAR0_Type_BitField (← (ID_ISAR0_read ())) 0b0001#4))
  (ID_ISAR0_write (_update_ID_ISAR0_Type_BitCount (← (ID_ISAR0_read ())) 0b0001#4))
  (ID_ISAR0_write (_update_ID_ISAR0_Type_Swap (← (ID_ISAR0_read ())) 0b0000#4))
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Jazelle (← (ID_ISAR1_read ())) 0b0001#4))
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Interwork (← (ID_ISAR1_read ())) 0b0011#4))
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Immediate (← (ID_ISAR1_read ())) 0b0001#4))
  (ID_ISAR1_write (_update_ID_ISAR1_Type_IfThen (← (ID_ISAR1_read ())) 0b0001#4))
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Extend (← (ID_ISAR1_read ())) 0b0010#4))
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Except_AR (← (ID_ISAR1_read ())) 0b0001#4))
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Except (← (ID_ISAR1_read ())) 0b0001#4))
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Endian (← (ID_ISAR1_read ())) 0b0001#4))
  (ID_ISAR2_write (_update_ID_ISAR2_Type_Reversal (← (ID_ISAR2_read ())) 0b0010#4))
  (ID_ISAR2_write (_update_ID_ISAR2_Type_PSR_AR (← (ID_ISAR2_read ())) 0b0001#4))
  (ID_ISAR2_write (_update_ID_ISAR2_Type_MultU (← (ID_ISAR2_read ())) 0b0010#4))
  (ID_ISAR2_write (_update_ID_ISAR2_Type_MultS (← (ID_ISAR2_read ())) 0b0011#4))
  (ID_ISAR2_write (_update_ID_ISAR2_Type_Mult (← (ID_ISAR2_read ())) 0b0010#4))
  (ID_ISAR2_write (_update_ID_ISAR2_Type_MultiAccessInt (← (ID_ISAR2_read ())) 0b0000#4))
  (ID_ISAR2_write (_update_ID_ISAR2_Type_MemHint (← (ID_ISAR2_read ())) 0b0100#4))
  (ID_ISAR2_write (_update_ID_ISAR2_Type_LoadStore (← (ID_ISAR2_read ())) 0b0010#4))
  (ID_ISAR3_write (_update_ID_ISAR3_Type_T32EE (← (ID_ISAR3_read ())) 0b0000#4))
  (ID_ISAR3_write (_update_ID_ISAR3_Type_TrueNOP (← (ID_ISAR3_read ())) 0b0001#4))
  (ID_ISAR3_write (_update_ID_ISAR3_Type_T32Copy (← (ID_ISAR3_read ())) 0b0001#4))
  (ID_ISAR3_write (_update_ID_ISAR3_Type_TabBranch (← (ID_ISAR3_read ())) 0b0001#4))
  (ID_ISAR3_write (_update_ID_ISAR3_Type_SynchPrim (← (ID_ISAR3_read ())) 0b0010#4))
  (ID_ISAR3_write (_update_ID_ISAR3_Type_SVC (← (ID_ISAR3_read ())) 0b0001#4))
  (ID_ISAR3_write (_update_ID_ISAR3_Type_SIMD (← (ID_ISAR3_read ())) 0b0011#4))
  (ID_ISAR3_write (_update_ID_ISAR3_Type_Saturate (← (ID_ISAR3_read ())) 0b0001#4))
  (ID_ISAR4_write (_update_ID_ISAR4_Type_SWP_frac (← (ID_ISAR4_read ())) 0b0000#4))
  (ID_ISAR4_write (_update_ID_ISAR4_Type_PSR_M (← (ID_ISAR4_read ())) 0b0000#4))
  (ID_ISAR4_write (_update_ID_ISAR4_Type_SynchPrim_frac (← (ID_ISAR4_read ())) 0b0000#4))
  (ID_ISAR4_write (_update_ID_ISAR4_Type_Barrier (← (ID_ISAR4_read ())) 0b0001#4))
  (ID_ISAR4_write (_update_ID_ISAR4_Type_SMC (← (ID_ISAR4_read ())) 0b0000#4))
  (ID_ISAR4_write (_update_ID_ISAR4_Type_Writeback (← (ID_ISAR4_read ())) 0b0001#4))
  (ID_ISAR4_write (_update_ID_ISAR4_Type_WithShifts (← (ID_ISAR4_read ())) 0b0100#4))
  (ID_ISAR4_write (_update_ID_ISAR4_Type_Unpriv (← (ID_ISAR4_read ())) 0b0010#4))
  writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR5_EL1) 7 4 0b0001#4)
  (ID_ISAR5_write (_update_ID_ISAR5_Type_VCMA (← (ID_ISAR5_read ())) 0b0001#4))
  (ID_ISAR5_write (_update_ID_ISAR5_Type_RDM (← (ID_ISAR5_read ())) 0b0001#4))
  (ID_ISAR5_write (_update_ID_ISAR5_Type_CRC32 (← (ID_ISAR5_read ())) 0b0000#4))
  (ID_ISAR5_write (_update_ID_ISAR5_Type_SHA2 (← (ID_ISAR5_read ())) 0b0001#4))
  (ID_ISAR5_write (_update_ID_ISAR5_Type_SHA1 (← (ID_ISAR5_read ())) 0b0001#4))
  (ID_ISAR5_write (_update_ID_ISAR5_Type_AES (← (ID_ISAR5_read ())) 0b0010#4))
  (ID_ISAR5_write (_update_ID_ISAR5_Type_SEVL (← (ID_ISAR5_read ())) 0b0001#4))
  (ID_ISAR6_write (_update_ID_ISAR6_Type_DP (← (ID_ISAR6_read ())) 0b0001#4))
  (ID_ISAR6_write (_update_ID_ISAR6_Type_BF16 (← (ID_ISAR6_read ())) 0b0001#4))
  (ID_ISAR6_write (_update_ID_ISAR6_Type_I8MM (← (ID_ISAR6_read ())) 0b0001#4))
  if ((← (IsFeatureImplemented FEAT_FP16)) : Bool)
  then
    (do
      (MVFR1_write (_update_MVFR1_Type_FPHP (← (MVFR1_read ())) 0b0011#4))
      (MVFR1_write (_update_MVFR1_Type_SIMDHP (← (MVFR1_read ())) 0b0010#4)))
  else
    (do
      (MVFR1_write (_update_MVFR1_Type_FPHP (← (MVFR1_read ())) 0b0010#4))
      (MVFR1_write (_update_MVFR1_Type_SIMDHP (← (MVFR1_read ())) 0b0001#4)))
  if ((HasArchVersion v8Ap3) : Bool)
  then
    (do
      (ID_MMFR4_write (_update_ID_MMFR4_Type_CCIDX (← (ID_MMFR4_read ())) 0b0001#4))
      (ID_ISAR6_write (_update_ID_ISAR6_Type_JSCVT (← (ID_ISAR6_read ())) 0b0001#4))
      (ID_DFR0_write (_update_ID_DFR0_Type_TraceFilt (← (ID_DFR0_read ())) 0b0001#4)))
  else (pure ())
  if ((HasArchVersion v8Ap4) : Bool)
  then
    (do
      writeReg EDPFR (Sail.BitVec.updateSubrange (← readReg EDPFR) 39 36 0b0001#4)
      (ID_ISAR6_write (_update_ID_ISAR6_Type_FHM (← (ID_ISAR6_read ())) 0b0001#4))
      (ID_PFR0_write (_update_ID_PFR0_Type_AMU (← (ID_PFR0_read ())) 0b0001#4))
      (ID_PFR0_write (_update_ID_PFR0_Type_DIT (← (ID_PFR0_read ())) 0b0001#4))
      (ID_DFR0_write (_update_ID_DFR0_Type_CopDbg (← (ID_DFR0_read ())) 0b1001#4))
      if ((←((pure (! (HaveEL EL3))) <&&> (do
           (pure ((_get_SCR_Type_NS (← readReg SCR)) == 1#1))))) : Bool)
      then (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg (← (ID_DFR0_read ())) 0b0000#4))
      else (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg (← (ID_DFR0_read ())) (_get_ID_DFR0_EL1_Type_CopDbg (← readReg ID_DFR0_EL1)))))
  else (pure ())
  if ((HasArchVersion v8Ap7) : Bool)
  then (ID_DFR0_write (_update_ID_DFR0_Type_PerfMon (← (ID_DFR0_read ())) 0b0111#4))
  else (pure ())
  if ((HasArchVersion v8Ap8) : Bool)
  then
    (do
      (ID_MMFR5_write (_update_ID_MMFR5_Type_ETS (← (ID_MMFR5_read ())) 0b0010#4))
      (ID_DFR0_write (_update_ID_DFR0_Type_CopDbg (← (ID_DFR0_read ())) 0b1010#4))
      if ((←((pure (! (HaveEL EL3))) <&&> (do
           (pure ((_get_SCR_Type_NS (← readReg SCR)) == 1#1))))) : Bool)
      then (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg (← (ID_DFR0_read ())) 0b0000#4))
      else (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg (← (ID_DFR0_read ())) (_get_ID_DFR0_Type_CopDbg (← (ID_DFR0_read ()))))))
  else (pure ())
  if ((HasArchVersion v8Ap6) : Bool)
  then
    (do
      (ID_PFR1_write (_update_ID_PFR1_Type_GenTimer (← (ID_PFR1_read ())) 0b0010#4))
      (ID_PFR0_write (_update_ID_PFR0_Type_AMU (← (ID_PFR0_read ())) 0b0010#4)))
  else (pure ())
  (ID_MMFR0_write (_update_ID_MMFR0_Type_InnerShr (← (ID_MMFR0_read ())) 0b0001#4))
  (ID_MMFR0_write (_update_ID_MMFR0_Type_FCSE (← (ID_MMFR0_read ())) 0b0000#4))
  (ID_MMFR0_write (_update_ID_MMFR0_Type_AuxReg (← (ID_MMFR0_read ())) 0b0010#4))
  (ID_MMFR0_write (_update_ID_MMFR0_Type_TCM (← (ID_MMFR0_read ())) 0b0000#4))
  (ID_MMFR0_write (_update_ID_MMFR0_Type_ShareLvl (← (ID_MMFR0_read ())) 0b0001#4))
  (ID_MMFR0_write (_update_ID_MMFR0_Type_OuterShr (← (ID_MMFR0_read ())) 0b0001#4))
  (ID_MMFR0_write (_update_ID_MMFR0_Type_PMSA (← (ID_MMFR0_read ())) 0b0000#4))
  (ID_MMFR0_write (_update_ID_MMFR0_Type_VMSA (← (ID_MMFR0_read ())) 0b0101#4))
  (ID_MMFR1_write (_update_ID_MMFR1_Type_BPred (← (ID_MMFR1_read ())) 0b0010#4))
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1TstCln (← (ID_MMFR1_read ())) 0b0000#4))
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1Uni (← (ID_MMFR1_read ())) 0b0000#4))
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1Hvd (← (ID_MMFR1_read ())) 0b0000#4))
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1UniSW (← (ID_MMFR1_read ())) 0b0000#4))
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1HvdSW (← (ID_MMFR1_read ())) 0b0000#4))
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1UniVA (← (ID_MMFR1_read ())) 0b0000#4))
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1HvdVA (← (ID_MMFR1_read ())) 0b0000#4))
  (ID_MMFR2_write (_update_ID_MMFR2_Type_HWAccFlg (← (ID_MMFR2_read ())) 0b0000#4))
  (ID_MMFR2_write (_update_ID_MMFR2_Type_WFIStall (← (ID_MMFR2_read ())) 0b0001#4))
  (ID_MMFR2_write (_update_ID_MMFR2_Type_MemBarr (← (ID_MMFR2_read ())) 0b0010#4))
  (ID_MMFR2_write (_update_ID_MMFR2_Type_UniTLB (← (ID_MMFR2_read ())) 0b0110#4))
  (ID_MMFR2_write (_update_ID_MMFR2_Type_HvdTLB (← (ID_MMFR2_read ())) 0b0000#4))
  (ID_MMFR2_write (_update_ID_MMFR2_Type_L1HvdRng (← (ID_MMFR2_read ())) 0b0000#4))
  (ID_MMFR2_write (_update_ID_MMFR2_Type_L1HvdBG (← (ID_MMFR2_read ())) 0b0000#4))
  (ID_MMFR2_write (_update_ID_MMFR2_Type_L1HvdFG (← (ID_MMFR2_read ())) 0b0000#4))
  (ID_MMFR3_write (_update_ID_MMFR3_Type_Supersec (← (ID_MMFR3_read ())) 0b0000#4))
  (ID_MMFR3_write (_update_ID_MMFR3_Type_CMemSz (← (ID_MMFR3_read ())) 0b0010#4))
  (ID_MMFR3_write (_update_ID_MMFR3_Type_CohWalk (← (ID_MMFR3_read ())) 0b0001#4))
  (ID_MMFR3_write (_update_ID_MMFR3_Type_PAN (← (ID_MMFR3_read ())) 0b0001#4))
  (ID_MMFR3_write (_update_ID_MMFR3_Type_MaintBcst (← (ID_MMFR3_read ())) 0b0010#4))
  (ID_MMFR3_write (_update_ID_MMFR3_Type_BPMaint (← (ID_MMFR3_read ())) 0b0010#4))
  (ID_MMFR3_write (_update_ID_MMFR3_Type_CMaintSW (← (ID_MMFR3_read ())) 0b0001#4))
  (ID_MMFR3_write (_update_ID_MMFR3_Type_CMaintVA (← (ID_MMFR3_read ())) 0b0001#4))
  (ID_PFR0_write (_update_ID_PFR0_Type_RAS (← (ID_PFR0_read ())) 0b0010#4))
  (ID_PFR0_write (_update_ID_PFR0_Type_State3 (← (ID_PFR0_read ())) 0b0000#4))
  (ID_PFR0_write (_update_ID_PFR0_Type_State2 (← (ID_PFR0_read ())) 0b0001#4))
  (ID_PFR0_write (_update_ID_PFR0_Type_State1 (← (ID_PFR0_read ())) 0b0011#4))
  (ID_PFR0_write (_update_ID_PFR0_Type_State0 (← (ID_PFR0_read ())) 0b0001#4))
  (ID_DFR1_write (_update_ID_DFR1_Type_MTPMU (← (ID_DFR1_read ())) 0b0001#4))
  if ((HasArchVersion v8Ap5) : Bool)
  then
    (do
      (ID_PFR0_write (_update_ID_PFR0_Type_CSV2 (← (ID_PFR0_read ())) 0b0001#4))
      (ID_DFR0_write (_update_ID_DFR0_Type_PerfMon (← (ID_DFR0_read ())) 0b0110#4)))
  else (pure ())
  (ID_DFR0_write (_update_ID_DFR0_Type_MMapTrc (← (ID_DFR0_read ())) 0b0001#4))
  (ID_DFR0_write (_update_ID_DFR0_Type_CopTrc (← (ID_DFR0_read ())) 0b0001#4))
  (ID_PFR1_write (_update_ID_PFR1_Type_GIC (← (ID_PFR1_read ())) 0b0000#4))
  (ID_PFR1_write (_update_ID_PFR1_Type_Virt_frac (← (ID_PFR1_read ())) 0b0000#4))
  (ID_PFR1_write (_update_ID_PFR1_Type_Sec_frac (← (ID_PFR1_read ())) 0b0000#4))
  (ID_PFR1_write (_update_ID_PFR1_Type_MProgMod (← (ID_PFR1_read ())) 0b0000#4))
  (ID_PFR1_write (_update_ID_PFR1_Type_ProgMod (← (ID_PFR1_read ())) 0b0000#4))
  (ID_PFR1_write (_update_ID_PFR1_Type_Security (← (ID_PFR1_read ())) 0b0000#4))
  (ID_PFR1_write (_update_ID_PFR1_Type_Virtualization (← (ID_PFR1_read ())) 0b0000#4))
  (MIDR_write (_update_MIDR_Type_Implementer (← (MIDR_read ())) 0b01000001#8))
  (MIDR_write (_update_MIDR_Type_Variant (← (MIDR_read ())) 0b0000#4))
  (MIDR_write (_update_MIDR_Type_Architecture (← (MIDR_read ())) 0b1111#4))
  (MIDR_write (_update_MIDR_Type_PartNum (← (MIDR_read ())) 0b110100001111#12))
  (MIDR_write (_update_MIDR_Type_Revision (← (MIDR_read ())) 0b0000#4))
  (VPIDR_write (_update_VPIDR_Type_Implementer (← (VPIDR_read ())) 0b01000001#8))
  (VPIDR_write (_update_VPIDR_Type_Variant (← (VPIDR_read ())) 0b0000#4))
  (VPIDR_write (_update_VPIDR_Type_Architecture (← (VPIDR_read ())) 0b1111#4))
  (VPIDR_write (_update_VPIDR_Type_PartNum (← (VPIDR_read ())) 0b110100001111#12))
  (VPIDR_write (_update_VPIDR_Type_Revision (← (VPIDR_read ())) 0b0000#4))
  (MPIDR_write (_update_MPIDR_Type_M (← (MPIDR_read ())) 1#1))
  (MPIDR_write (_update_MPIDR_Type_U (← (MPIDR_read ())) 0#1))
  (MPIDR_write (_update_MPIDR_Type_MT (← (MPIDR_read ())) 0#1))
  (MPIDR_write (_update_MPIDR_Type_Aff2 (← (MPIDR_read ())) 0b00000000#8))
  (MPIDR_write (_update_MPIDR_Type_Aff1 (← (MPIDR_read ())) 0b00000000#8))
  (MPIDR_write (_update_MPIDR_Type_Aff0 (← (MPIDR_read ())) 0b00000000#8))
  (MVFR0_write (_update_MVFR0_Type_FPRound (← (MVFR0_read ())) 0b0001#4))
  (MVFR0_write (_update_MVFR0_Type_FPShVec (← (MVFR0_read ())) 0b0000#4))
  (MVFR0_write (_update_MVFR0_Type_FPSqrt (← (MVFR0_read ())) 0b0001#4))
  (MVFR0_write (_update_MVFR0_Type_FPDivide (← (MVFR0_read ())) 0b0001#4))
  (MVFR0_write (_update_MVFR0_Type_FPTrap (← (MVFR0_read ())) 0b0001#4))
  (MVFR0_write (_update_MVFR0_Type_FPDP (← (MVFR0_read ())) 0b0010#4))
  (MVFR0_write (_update_MVFR0_Type_FPSP (← (MVFR0_read ())) 0b0010#4))
  (MVFR0_write (_update_MVFR0_Type_SIMDReg (← (MVFR0_read ())) 0b0010#4))
  (MVFR1_write (_update_MVFR1_Type_SIMDFMAC (← (MVFR1_read ())) 0b0001#4))
  (MVFR1_write (_update_MVFR1_Type_SIMDSP (← (MVFR1_read ())) 0b0001#4))
  (MVFR1_write (_update_MVFR1_Type_SIMDInt (← (MVFR1_read ())) 0b0001#4))
  (MVFR1_write (_update_MVFR1_Type_SIMDLS (← (MVFR1_read ())) 0b0001#4))
  (MVFR1_write (_update_MVFR1_Type_FPDNaN (← (MVFR1_read ())) 0b0001#4))
  (MVFR1_write (_update_MVFR1_Type_FPFtZ (← (MVFR1_read ())) 0b0001#4))
  (MVFR2_write (_update_MVFR2_Type_FPMisc (← (MVFR2_read ())) 0b0100#4))
  (MVFR2_write (_update_MVFR2_Type_SIMDMisc (← (MVFR2_read ())) 0b0011#4))
  writeReg TLBTR (Sail.BitVec.updateSubrange (← readReg TLBTR) 0 0 0#1)
  (HSCTLR_write (_update_HSCTLR_Type_EE (← (HSCTLR_read ())) 0#1))
  (SCTLR_write (_update_SCTLR_Type_TE (← (SCTLR_read__2 ())) (_get_Configuration_Type_ExceptInit (← readReg _ConfigReg))))
  (SCTLR_write (_update_SCTLR_Type_EE (← (SCTLR_read__2 ())) (_get_Configuration_Type_CFGEND (← readReg _ConfigReg))))
  (SCTLR_write (_update_SCTLR_Type_SPAN (← (SCTLR_read__2 ())) 0#1))
  (SCTLR_write (_update_SCTLR_Type_V (← (SCTLR_read__2 ())) 0#1))
  (SCTLR_write (_update_SCTLR_Type_UNK (← (SCTLR_read__2 ())) 0#1))
  (FPEXC_write (_update_FPEXC_Type_EX (← (FPEXC_read ())) 0#1))
  (FPEXC_write (_update_FPEXC_Type_FP2V (← (FPEXC_read ())) 0#1))
  (FPEXC_write (_update_FPEXC_Type_VV (← (FPEXC_read ())) 0#1))
  (FPEXC_write (_update_FPEXC_Type_TFV (← (FPEXC_read ())) 0#1))
  (FPEXC_write (_update_FPEXC_Type_VECITR (← (FPEXC_read ())) 0b111#3))
  (HTCR_write (_update_HTCR_Type_HWU62 (← (HTCR_read ())) 0#1))
  (HTCR_write (_update_HTCR_Type_HWU61 (← (HTCR_read ())) 0#1))
  (HTCR_write (_update_HTCR_Type_HWU60 (← (HTCR_read ())) 0#1))
  (HTCR_write (_update_HTCR_Type_HWU59 (← (HTCR_read ())) 0#1))
  (HTCR_write (_update_HTCR_Type_HPD (← (HTCR_read ())) 0#1))
  (HTCR_write (_update_HTCR_Type_SH0 (← (HTCR_read ())) 0b00#2))
  (HTCR_write (_update_HTCR_Type_ORGN0 (← (HTCR_read ())) 0b00#2))
  (HTCR_write (_update_HTCR_Type_IRGN0 (← (HTCR_read ())) 0b00#2))
  (HTCR_write (_update_HTCR_Type_T0SZ (← (HTCR_read ())) 0b000#3))
  (NMRR_write (Mk_NMRR_Type (Sail.BitVec.updateSubrange (← (NMRR_read ())) 31 16 0b0100010011100000#16)))
  (NMRR_write (Mk_NMRR_Type (Sail.BitVec.updateSubrange (← (NMRR_read ())) 15 0 0b0100100011100000#16)))
  writeReg NSACR (Sail.BitVec.updateSubrange (← readReg NSACR) 11 11 0#1)
  writeReg NSACR (Sail.BitVec.updateSubrange (← readReg NSACR) 10 10 0#1)
  (PRRR_write (Mk_PRRR_Type (Sail.BitVec.updateSubrange (← (PRRR_read ())) 31 24 (Zeros (n := 8)))))
  (PRRR_write (_update_PRRR_Type_NS1 (← (PRRR_read ())) 1#1))
  (PRRR_write (_update_PRRR_Type_NS0 (← (PRRR_read ())) 0#1))
  (PRRR_write (_update_PRRR_Type_DS1 (← (PRRR_read ())) 0#1))
  (PRRR_write (_update_PRRR_Type_DS0 (← (PRRR_read ())) 1#1))
  (PRRR_write (Mk_PRRR_Type (Sail.BitVec.updateSubrange (← (PRRR_read ())) 15 0 0b1000101010100100#16)))
  writeReg DBGDIDR (Sail.BitVec.updateSubrange (← readReg DBGDIDR) 31 28 (integer_subrange ((← readReg NUM_WATCHPOINTS) -i 1) 3 0))
  writeReg DBGDIDR (Sail.BitVec.updateSubrange (← readReg DBGDIDR) 27 24 (integer_subrange ((← readReg NUM_BREAKPOINTS) -i 1) 3 0))
  writeReg DBGDIDR (Sail.BitVec.updateSubrange (← readReg DBGDIDR) 23 20 (integer_subrange ((← readReg __num_ctx_breakpoints) -i 1) 3 0))
  if ((HasArchVersion v8Ap2) : Bool)
  then writeReg DBGDIDR (Sail.BitVec.updateSubrange (← readReg DBGDIDR) 19 16 0b1000#4)
  else (pure ())
  if ((HasArchVersion v8Ap4) : Bool)
  then writeReg DBGDIDR (Sail.BitVec.updateSubrange (← readReg DBGDIDR) 19 16 0b1001#4)
  else (pure ())
  if ((HasArchVersion v8Ap8) : Bool)
  then
    (do
      writeReg DBGDIDR (Sail.BitVec.updateSubrange (← readReg DBGDIDR) 19 16 0b1010#4)
      (ID_DFR0_write (_update_ID_DFR0_Type_PerfMon (← (ID_DFR0_read ())) 0b1000#4)))
  else (pure ())
  writeReg DBGDIDR (Sail.BitVec.updateSubrange (← readReg DBGDIDR) 14 14 1#1)
  writeReg DBGDIDR (Sail.BitVec.updateSubrange (← readReg DBGDIDR) 12 12 1#1)
  writeReg DBGDEVID (Sail.BitVec.updateSubrange (← readReg DBGDEVID) 7 4 0b0001#4)
  writeReg DBGDEVID (Sail.BitVec.updateSubrange (← readReg DBGDEVID) 11 8 0b1111#4)
  writeReg DBGDEVID (Sail.BitVec.updateSubrange (← readReg DBGDEVID) 15 12 0b0000#4)
  writeReg DBGDEVID (Sail.BitVec.updateSubrange (← readReg DBGDEVID) 19 16 0b0001#4)
  writeReg DBGDEVID (Sail.BitVec.updateSubrange (← readReg DBGDEVID) 27 24 0b0001#4)
  (HDCR_write (_update_HDCR_Type_HPMN (← (HDCR_read ())) (_get_PMCR_Type_N (← (PMCR_read ())))))
  writeReg ICC_MSRE (Sail.BitVec.updateSubrange (← readReg ICC_MSRE) 0 0 1#1)
  (ICC_HSRE_write (_update_ICC_HSRE_Type_SRE (← (ICC_HSRE_read ())) 1#1))
  writeReg JMCR (Zeros (n := 32))
  writeReg JOSCR (Zeros (n := 32))
  writeReg JIDR (Zeros (n := 32))
  (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLM (← (DBGOSLSR_read ())) 0b10#2))
  (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ())) 1#1))
  (HCPTR_write (_update_HCPTR_Type_TCPAC (← (HCPTR_read ())) 0#1))
  (HCPTR_write (_update_HCPTR_Type_TTA (← (HCPTR_read ())) 0#1))
  (HCPTR_write (_update_HCPTR_Type_TASE (← (HCPTR_read ())) 0#1))
  (HCPTR_write (_update_HCPTR_Type_TCP11 (← (HCPTR_read ())) 0#1))
  (HCPTR_write (_update_HCPTR_Type_TCP10 (← (HCPTR_read ())) 0#1))
  if ((HasArchVersion v9Ap4) : Bool)
  then
    (do
      (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg (← (ID_DFR0_read ())) 0b1011#4))
      (ID_DFR0_write (_update_ID_DFR0_Type_CopDbg (← (ID_DFR0_read ())) 0b1011#4))
      (ID_DFR0_write (_update_ID_DFR0_Type_PerfMon (← (ID_DFR0_read ())) 0b1001#4))
      (ID_ISAR6_write (_update_ID_ISAR6_Type_SPECRES (← (ID_ISAR6_read ())) 0b0010#4))
      (ID_ISAR6_write (Mk_ID_ISAR6_Type (Sail.BitVec.updateSubrange (← (ID_ISAR6_read ())) 31 28 0b0001#4)))
      writeReg DBGDIDR (Sail.BitVec.updateSubrange (← readReg DBGDIDR) 19 16 0b1011#4)
      writeReg EDDEVID1 (Sail.BitVec.updateSubrange (← readReg EDDEVID1) 7 4 0b0010#4))
  else (pure ())

def PAR_EL1_read (_ : Unit) : SailM (BitVec 128) := do
  let r ← (( do readReg _PAR_EL1 ) : SailM PAR_EL1_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (← (PAR_read ())) 0 64)))

def PAR_EL1_write (value_name : (BitVec 128)) : SailM Unit := do
  let r : PAR_EL1_Type := value_name
  (PAR_write (Mk_PAR_Type (set_slice 64 (← (PAR_read ())) 0 (BitVec.slice r 0 64))))
  writeReg _PAR_EL1 r

/-- Type quantifiers: ec : Int -/
def AArch64_SystemAccessTrapSyndrome (instr_in : (BitVec 32)) (ec : Int) : SailM ExceptionRecord := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  let instr : (BitVec 32) := instr_in
  match ec with
  | 0 => (do (ExceptionSyndrome Exception_Uncategorized))
  | 7 =>
    (do
      let except ← (ExceptionSyndrome Exception_AdvSIMDFPAccessTrap)
      (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 24 20 (← (ConditionSyndrome ()))))) }))
  | 20 =>
    (do
      let except ← (ExceptionSyndrome Exception_SystemRegister128Trap)
      let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 21 20 (Sail.BitVec.extractLsb instr 20 19)) }
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 17 (Sail.BitVec.extractLsb instr 7 5)) }
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 16 14 (Sail.BitVec.extractLsb instr 18 16)) }
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 13 10 (Sail.BitVec.extractLsb instr 15 12)) }
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 6 (Sail.BitVec.extractLsb instr 4 1)) }
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 1 (Sail.BitVec.extractLsb instr 11 8)) }
      (pure { except with syndrome := (BitVec.update except.syndrome 0 (Bit (BitVec.join1 [(BitVec.access instr 21)]))) }))
  | 24 =>
    (do
      let except ← (ExceptionSyndrome Exception_SystemRegisterTrap)
      let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 21 20 (Sail.BitVec.extractLsb instr 20 19)) }
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 17 (Sail.BitVec.extractLsb instr 7 5)) }
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 16 14 (Sail.BitVec.extractLsb instr 18 16)) }
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 13 10 (Sail.BitVec.extractLsb instr 15 12)) }
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5 (Sail.BitVec.extractLsb instr 4 0)) }
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 1 (Sail.BitVec.extractLsb instr 11 8)) }
      (pure { except with syndrome := (BitVec.update except.syndrome 0 (Bit (BitVec.join1 [(BitVec.access instr 21)]))) }))
  | 25 => (do (ExceptionSyndrome Exception_SVEAccessTrap))
  | 29 => (do (ExceptionSyndrome Exception_SMEAccessTrap))
  | _ =>
    (do
      (Unreachable ())
      (pure except))


