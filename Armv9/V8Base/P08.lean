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

def AArch64_IMPDEFResets (_ : Unit) : SailM Unit := do
  writeReg DCZID_EL0 (Sail.BitVec.updateSubrange (← readReg DCZID_EL0) 4 4 0#1)
  writeReg DCZID_EL0 (Sail.BitVec.updateSubrange (← readReg DCZID_EL0) 3 0 (integer_subrange (← readReg __dczid_log2_block_size) 3 0))
  writeReg ERRIDR_EL1 (Sail.BitVec.updateSubrange (← readReg ERRIDR_EL1) 15 0 (Sail.BitVec.zeroExtend 0x4#4 16))
  let loop_i_lower := 0
  let loop_i_upper ← do (pure ((BitVec.toNat (_get_ERRIDR_EL1_Type_NUM (← readReg ERRIDR_EL1))) -i 1))
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      sail_assert ((0 ≤b i) && (i <b 4)) "src/reset.sail:432.55-432.56"
      writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) i (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) i) 54 53 0b11#2))
      writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) i (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) i) 52 52 1#1))
      writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) i (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) i) 51 51 1#1))
      writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) i (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) i) 50 50 1#1))
      writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) i (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) i) 49 49 1#1))
      writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) i (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) i) 48 48 1#1))
      writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) i (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) i) 31 31 1#1))
  (pure loop_vars)
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 25 24 0b01#2))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 23 22 0b10#2))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 21 20 0b01#2))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 19 18 0b01#2))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 17 16 0b10#2))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 15 15 1#1))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 14 12 0b100#3))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 11 10 0b10#2))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 9 8 0b11#2))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 7 6 0b10#2))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 5 4 0b11#2))
  writeReg ERRnFR (vectorUpdate (← readReg ERRnFR) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg ERRnFR) 0) 1 0 0b10#2))
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 31 24 (Zeros (n := 8)))
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 23 16
    (← (do
      if ((IsZero (_get_PMCR_EL0_Type_IMP (← readReg PMCR_EL0))) : Bool)
      then (pure (Zeros (n := 8)))
      else (pure CFG_PMCR_IDCODE))))
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 15 11 (integer_subrange (← readReg NUM_PMU_COUNTERS) 4 0))
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 2 2 0#1)
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 1 1 0#1)
  writeReg PMCEID0_EL0 (Mk_PMCEID0_EL0_Type (Sail.BitVec.zeroExtend 0b111101001000000000100000000100000001#36 64))
  writeReg PMCEID1_EL0 (Mk_PMCEID1_EL0_Type (Zeros (n := 64)))
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
  writeReg CNTFID0 (Mk_CNTFID0_Type (← readReg __CNTbase_frequency))
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 51 48 0b0001#4)
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 39 36 0b1111#4)
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 35 32 0b0010#4)
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 43 40 0b0001#4)
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 31 28 (integer_subrange ((← readReg __num_ctx_breakpoints) -i 1) 3 0))
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 23 20 (integer_subrange ((← readReg NUM_WATCHPOINTS) -i 1) 3 0))
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 15 12 (integer_subrange ((← readReg NUM_BREAKPOINTS) -i 1) 3 0))
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 7 4 0b0001#4)
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 3 0 0b1001#4)
  if ((← (IsFeatureImplemented FEAT_RME)) : Bool)
  then
    (do
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 55 52 0b0001#4)
      writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange (← readReg GPCCR_EL3) 23 20 (← readReg __rme_l0gptsz)))
  else writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 55 52 0b0000#4)
  if ((← (IsFeatureImplemented FEAT_BRBE)) : Bool)
  then
    (do
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 55 52 0b0010#4)
      writeReg BRBIDR0_EL1 (Sail.BitVec.updateSubrange (← readReg BRBIDR0_EL1) 15 12 0b0101#4)
      writeReg BRBIDR0_EL1 (Sail.BitVec.updateSubrange (← readReg BRBIDR0_EL1) 11 8 0b0000#4)
      writeReg BRBIDR0_EL1 (Sail.BitVec.updateSubrange (← readReg BRBIDR0_EL1) 7 0 (integer_subrange (← readReg NUM_BRBE_RECORDS) 7 0)))
  else (pure ())
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 47 44 0b0000#4)
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 43 40 0b0000#4)
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 39 36 0b0000#4)
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 35 32 0b0000#4)
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 31 28 0b0000#4)
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 23 20 0b0000#4)
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 19 16 0b0000#4)
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 15 12 0b0001#4)
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 11 8 0b0001#4)
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 7 4 0b0010#4)
  writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 3 0 0b0000#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 43 40 0b0011#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 35 32 0b0011#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 39 36 0b0010#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 47 44 0b0001#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 59 56 0b0001#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 63 60 0b0010#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 31 28 0b0001#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 23 20 0b0010#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 27 24 0b0000#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 19 16 0b0000#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 15 12 0b0001#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 11 8 0b0001#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 7 4 0b0010#4)
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 3 0 (← (EncodePARange ())))
  writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 19 16 (← (EncodeVARange ())))
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 31 28 0b0000#4)
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 27 24 0b0000#4)
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 23 20 0b0000#4)
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 19 16 0b0000#4)
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 11 8 0b0000#4)
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 15 12 0b0000#4)
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 7 4 0b0000#4)
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 3 0 0b0000#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 35 32 0b0001#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 15 12 0b0001#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 11 8 0b0001#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 7 4 0b0001#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 3 0 0b0010#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 63 60 0b0001#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 59 56 0b0010#4)
  writeReg ID_PFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR2_EL1) 3 0 0b0001#4)
  writeReg ID_PFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR2_EL1) 7 4 0b0001#4)
  if ((← (HaveCNTSCExt ())) : Bool)
  then writeReg CNTID (Sail.BitVec.updateSubrange (← readReg CNTID) 3 0 0b0001#4)
  else (pure ())
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 47 44 0b0001#4)
  writeReg AMCIDR0 (Sail.BitVec.updateSubrange (← readReg AMCIDR0) 7 0 0b00001101#8)
  writeReg AMCIDR1 (Sail.BitVec.updateSubrange (← readReg AMCIDR1) 7 4 0b1001#4)
  writeReg AMCIDR2 (Sail.BitVec.updateSubrange (← readReg AMCIDR2) 7 0 0b00000101#8)
  writeReg AMCIDR3 (Sail.BitVec.updateSubrange (← readReg AMCIDR3) 7 0 0b10110001#8)
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCFGR_EL0) 7 0 0b00010011#8)
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCFGR_EL0) 13 8 0b111111#6)
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCFGR_EL0) 24 24 1#1)
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCFGR_EL0) 31 28 (integer_subrange ((← readReg NUM_AMU_COUNTER_GROUPS) -i 1) 3 0))
  writeReg AMCGCR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCGCR_EL0) 7 0 (integer_subrange (← readReg NUM_AMU_CG0_MONITORS) 7 0))
  writeReg AMCGCR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCGCR_EL0) 15 8 (integer_subrange (← readReg NUM_AMU_CG1_MONITORS) 7 0))
  writeReg AMDEVARCH (Sail.BitVec.updateSubrange (← readReg AMDEVARCH) 31 21 (0b0100#4 +++ 0b0111011#7))
  writeReg AMDEVARCH (Sail.BitVec.updateSubrange (← readReg AMDEVARCH) 20 20 1#1)
  writeReg AMDEVARCH (Sail.BitVec.updateSubrange (← readReg AMDEVARCH) 15 0 (0b0000#4 +++ 0b101001100110#12))
  writeReg AMDEVTYPE (Sail.BitVec.updateSubrange (← readReg AMDEVTYPE) 7 4 0b0001#4)
  writeReg AMDEVTYPE (Sail.BitVec.updateSubrange (← readReg AMDEVTYPE) 3 0 0b0110#4)
  writeReg AMEVTYPER0_EL0 (vectorUpdate (← readReg AMEVTYPER0_EL0) 0 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 0) 15 0 0b0000000000010001#16))
  writeReg AMEVTYPER0_EL0 (vectorUpdate (← readReg AMEVTYPER0_EL0) 1 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 1) 15 0 0b0100000000000100#16))
  writeReg AMEVTYPER0_EL0 (vectorUpdate (← readReg AMEVTYPER0_EL0) 2 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 2) 15 0 0b0000000000001000#16))
  writeReg AMEVTYPER0_EL0 (vectorUpdate (← readReg AMEVTYPER0_EL0) 3 (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg AMEVTYPER0_EL0) 3) 15 0 0b0100000000000101#16))
  writeReg AMIIDR (Sail.BitVec.updateSubrange (← readReg AMIIDR) 11 0 0b010000111011#12)
  writeReg AMPIDR1 (Sail.BitVec.updateSubrange (← readReg AMPIDR1) 7 4 0b1011#4)
  writeReg AMPIDR2 (Sail.BitVec.updateSubrange (← readReg AMPIDR2) 3 3 1#1)
  writeReg AMPIDR2 (Sail.BitVec.updateSubrange (← readReg AMPIDR2) 2 0 0b011#3)
  writeReg AMPIDR4 (Sail.BitVec.updateSubrange (← readReg AMPIDR4) 3 0 0b0100#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 51 48 0b0001#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 31 28 0b0000#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 27 24 0b0000#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 23 20 0b0000#4)
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 19 16 0b0000#4)
  writeReg MPIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPIDR_EL1) 31 0 (← readReg CFG_MPIDR))
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange (← readReg VMPIDR_EL2) 39 32 0b00000000#8)
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange (← readReg VMPIDR_EL2) 30 30 0#1)
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange (← readReg VMPIDR_EL2) 24 24 0#1)
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange (← readReg VMPIDR_EL2) 23 16 0b00000000#8)
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange (← readReg VMPIDR_EL2) 15 8 0b00000000#8)
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange (← readReg VMPIDR_EL2) 7 0 0b00000000#8)
  (VMPIDR_write (_update_VMPIDR_Type_M (← (VMPIDR_read ())) 1#1))
  if ((HasArchVersion v8Ap1) : Bool)
  then
    (do
      writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR5_EL1) 27 24 0b0001#4)
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 23 20 0b0010#4)
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 31 28 0b0001#4)
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 19 16 0b0001#4)
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 11 8 0b0001#4)
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 15 12 0b0001#4)
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 3 0 0b0010#4))
  else (pure ())
  if ((← (IsFeatureImplemented FEAT_CRC32)) : Bool)
  then
    (do
      writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR5_EL1) 19 16 0b0001#4)
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 19 16 0b0001#4))
  else (pure ())
  if ((← (IsFeatureImplemented FEAT_VMID16)) : Bool)
  then writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 7 4 0b0010#4)
  else (pure ())
  if ((← (IsFeatureImplemented FEAT_PAN)) : Bool)
  then
    (do
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 23 20 0b0001#4)
      writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR3_EL1) 19 16 0b0001#4))
  else (pure ())
  if ((! (← (IsFeatureImplemented FEAT_AES))) : Bool)
  then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 7 4 0b0000#4)
  else (pure ())
  if ((← (IsFeatureImplemented FEAT_AES)) : Bool)
  then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 7 4 0b0001#4)
  else (pure ())
  if ((←((IsFeatureImplemented FEAT_AES) <&&> (do
       (IsFeatureImplemented FEAT_PMULL)))) : Bool)
  then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 7 4 0b0010#4)
  else (pure ())
  if ((! (← (IsFeatureImplemented FEAT_SHA1))) : Bool)
  then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 11 8 0b0000#4)
  else (pure ())
  if ((! (← (IsFeatureImplemented FEAT_SHA256))) : Bool)
  then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 15 12 0b0000#4)
  else (pure ())
  if ((HasArchVersion v8Ap2) : Bool)
  then
    (do
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 31 28 0b0001#4)
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 23 20 0b0010#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 3 0 0b0001#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 7 4 0b0001#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 11 8 0b0001#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 15 12 0b0001#4)
      writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR3_EL1) 19 16 0b0010#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 39 36 0b0001#4)
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR4_EL1) 11 8 0b0001#4)
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR4_EL1) 15 12 0b0001#4)
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR4_EL1) 23 20 0b0001#4)
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR4_EL1) 7 4 0b0001#4)
      if ((HaveEL EL2) : Bool)
      then
        (do
          writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR4_EL1) 31 28 0b0010#4)
          writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 59 56 0b0010#4))
      else
        (do
          writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR4_EL1) 31 28 0b0000#4)
          writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 59 56 0b0000#4))
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR4_EL1) 31 28 0b0000#4)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 63 63 1#1)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 32 32 1#1)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 34 34 1#1)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 35 35 1#1)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 39 36 0b1111#4)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 48 48 1#1)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 55 52 0b1111#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 43 40 0b0001#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 39 36 0b0001#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 3 0 0b0010#4)
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR6_EL1) 7 4 0b0001#4)
      if ((← (HaveDoPD ())) : Bool)
      then
        (do
          writeReg EDDEVID (Sail.BitVec.updateSubrange (← readReg EDDEVID) 7 4 0b0001#4)
          writeReg CTIDEVARCH (Sail.BitVec.updateSubrange (← readReg CTIDEVARCH) 19 16 0b0001#4))
      else
        (do
          writeReg EDDEVID (Sail.BitVec.updateSubrange (← readReg EDDEVID) 7 4 0b0000#4)
          writeReg CTIDEVARCH (Sail.BitVec.updateSubrange (← readReg CTIDEVARCH) 19 16 0b0000#4))
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 43 40 0b0001#4)
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 35 32 0b0001#4)
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 19 16 0b0001#4)
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 7 4 0b0010#4)
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 3 0 0b0001#4)
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 23 20 0b0001#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 47 44 0b0001#4)
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 23 20 0b0010#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 47 44 0b0010#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 51 48 0b0001#4)
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR6_EL1) 23 20 0b0001#4)
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 47 44 0b0001#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 55 52 0b0001#4)
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR6_EL1) 27 24 0b0001#4))
  else (pure ())
  if ((HasArchVersion v8Ap6) : Bool)
  then
    (do
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 47 44 0b0010#4)
      writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR0_EL1) 23 20 0b0010#4)
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 55 52 0b0001#4)
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 59 56 0b0001#4))
  else (pure ())
  if ((← (IsFeatureImplemented FEAT_DotProd)) : Bool)
  then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 47 44 0b0001#4)
  else (pure ())
  if ((← (IsFeatureImplemented FEAT_FP16)) : Bool)
  then
    (do
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 19 16 0b0001#4)
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 23 20 0b0001#4))
  else (pure ())
  if ((← (IsFeatureImplemented FEAT_AA32HPD)) : Bool)
  then
    (do
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 15 12 0b0010#4)
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR4_EL1) 19 16 0b0010#4))
  else (pure ())
  if ((← (HaveMPAMExt ())) : Bool)
  then
    (do
      if ((← readReg __empam_force_ns_implemented) : Bool)
      then
        (do
          writeReg __mpam_major CFG_MPAM_v0p1
          writeReg __mpam_frac CFG_MPAM_frac_v0p1
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPAMIDR_EL1) 60 60 1#1))
      else
        (do
          writeReg __mpam_major CFG_MPAM_v1p1
          writeReg __mpam_frac CFG_MPAM_frac_v1p1)
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 43 40 (← readReg __mpam_major))
      writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPAMIDR_EL1) 15 0 (← readReg __mpam_partid_max))
      writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPAMIDR_EL1) 39 32 (← readReg __mpam_pmg_max))
      if ((← readReg __mpam_has_hcr) : Bool)
      then
        (do
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPAMIDR_EL1) 17 17 1#1)
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPAMIDR_EL1) 20 18 (← readReg __mpam_vpmr_max)))
      else (pure ())
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 19 16 (← readReg __mpam_frac))
      sail_assert (←((pure ((BitVec.toNat (_get_ID_AA64PFR0_EL1_Type_MPAM (← readReg ID_AA64PFR0_EL1))) >b 1)) <||> (do
        (do
          let b__0 ← do (pure (_get_ID_AA64PFR0_EL1_Type_MPAM (← readReg ID_AA64PFR0_EL1)))
          if (((Sail.BitVec.extractLsb b__0 3 1) == (0b000#3 : (BitVec 3))) : Bool)
          then (pure true)
          else (pure false)) <&&> (do
          (pure ((_get_ID_AA64PFR1_EL1_Type_MPAM_frac (← readReg ID_AA64PFR1_EL1)) == 0b0001#4)))))) "src/reset.sail:720.56-720.57"
      if ((← readReg __empam_sdeflt_implemented) : Bool)
      then writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPAMIDR_EL1) 61 61 1#1)
      else (pure ())
      if ((← readReg __empam_tidr_implemented) : Bool)
      then writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPAMIDR_EL1) 58 58 1#1)
      else (pure ()))
  else (pure ())
  if ((←((pure (HasArchVersion v9Ap2)) <&&> (do
       (HaveRME ())))) : Bool)
  then
    (do
      writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPAMIDR_EL1) 59 59 1#1)
      if ((← readReg __mpam_has_altsp) : Bool)
      then writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPAMIDR_EL1) 57 57 1#1)
      else (pure ()))
  else (pure ())
  if ((HasArchVersion v8Ap3) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_PACQARMA3)) : Bool)
      then
        (do
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 11 8 0b0001#4)
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 15 12 0b0101#4)
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 7 4 0b0000#4)
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 27 24 0b0000#4))
      else (pure ())
      if ((← (IsFeatureImplemented FEAT_PACQARMA5)) : Bool)
      then
        (do
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 11 8 0b0000#4)
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 15 12 0b0000#4)
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 7 4 0b0101#4)
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 27 24 0b0001#4))
      else (pure ())
      if ((← (IsFeatureImplemented FEAT_CONSTPACFIELD)) : Bool)
      then writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 27 24 0b0001#4)
      else writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 27 24 0b0000#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 15 12 0b0001#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 19 16 0b0001#4)
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR6_EL1) 3 0 0b0001#4)
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR4_EL1) 27 24 0b0001#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 27 24 0b0001#4)
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 31 28 0b0001#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 23 20 0b0001#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 23 20 0b0001#4))
  else (pure ())
  if ((HasArchVersion v8Ap4) : Bool)
  then
    (do
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 23 20 0b0010#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 31 28 0b0001#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 35 32 0b0001#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 51 48 0b0001#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 43 40 0b0001#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 27 24 0b0010#4)
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 3 0 0b1001#4)
      if ((←((pure (! (HaveEL EL3))) <&&> (do
           (pure ((_get_SCR_Type_NS (← readReg SCR)) == 1#1))))) : Bool)
      then writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 7 4 0b0000#4)
      else writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 7 4 (_get_ID_DFR0_EL1_Type_CopDbg (← readReg ID_DFR0_EL1)))
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 39 36 0b0001#4)
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 59 56 0b0010#4)
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 55 52 0b0000#4)
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 51 48 0b0001#4)
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR6_EL1) 11 8 0b0001#4)
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 31 28 0b0010#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 55 52 (integer_subrange (← readReg __block_bbm_implemented) 3 0))
      if ((← (IsFeatureImplemented FEAT_SHA512)) : Bool)
      then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 15 12 0b0010#4)
      else (pure ())
      if ((← (IsFeatureImplemented FEAT_SHA3)) : Bool)
      then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 35 32 0b0001#4)
      else (pure ())
      if ((← (IsFeatureImplemented FEAT_SM3)) : Bool)
      then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 39 36 0b0001#4)
      else (pure ())
      if ((← (IsFeatureImplemented FEAT_SM4)) : Bool)
      then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 43 40 0b0001#4)
      else (pure ())
      if ((← (HavePMUv3p4 ())) : Bool)
      then
        (do
          if ((← (HavePMUv3TH ())) : Bool)
          then writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange (← readReg PMMIR_EL1) 23 20 0b1100#4)
          else (pure ())
          writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange (← readReg PMMIR_EL1) 19 16 0b0100#4)
          writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange (← readReg PMMIR_EL1) 15 8 0b00000011#8))
      else (pure ()))
  else (pure ())
  writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 7 4 0b0010#4)
  if ((HasArchVersion v8Ap5) : Bool)
  then
    (do
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 55 52 0b0010#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 35 32 0b0001#4)
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 3 0 0b0001#4)
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 27 24 0b0110#4)
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 63 60 0b0001#4)
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 63 60 0b0001#4)
      if ((← (HaveMTE2Ext ())) : Bool)
      then writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 11 8 0b0010#4)
      else (pure ())
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 11 8 0b0110#4)
      writeReg EDDFR (Sail.BitVec.updateSubrange (← readReg EDDFR) 11 8 0b0000#4)
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR6_EL1) 15 12 0b0001#4)
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR6_EL1) 19 16 0b0001#4))
  else (pure ())
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 23 20 0b0000#4)
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 11 8 0b0000#4)
  if ((HasArchVersion v8Ap6) : Bool)
  then writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 35 32 0b0001#4)
  else (pure ())
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR1_EL1) 19 16 0b0010#4)
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 51 48 0b0001#4)
  writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR1_EL1) 3 0 0b0001#4)
  if ((HasArchVersion v8Ap7) : Bool)
  then
    (do
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 43 40 0b0001#4)
      if (((! (HaveEL EL3)) && (HaveEL EL2)) : Bool)
      then writeReg HCRX_EL2 (Mk_HCRX_EL2_Type (Zeros (n := 64)))
      else (pure ())
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 47 44 0b0001#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 11 8 0b0111#4)
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 27 24 0b0111#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 35 32 0b0011#4)
      if ((← readReg __feat_rpres) : Bool)
      then writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 7 4 0b0001#4)
      else (pure ())
      if ((← (Have52BitIPAAndPASpaceExt ())) : Bool)
      then
        (do
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 31 28 0b0001#4)
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 43 40 0b0011#4)
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 23 20 0b0010#4)
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 35 32 0b0011#4))
      else (pure ())
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 59 56 0b0001#4)
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 3 0 0b0010#4)
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 23 20 0b0011#4)
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 11 8 0b0011#4)
      if ((← (HaveFeatLS64_ACCDATA ())) : Bool)
      then writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 63 60 0b0011#4)
      else
        (do
          if ((← (HaveFeatLS64_V ())) : Bool)
          then writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 63 60 0b0010#4)
          else
            (do
              if ((← (HaveFeatLS64 ())) : Bool)
              then writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 63 60 0b0001#4)
              else writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 63 60 0b0000#4))))
  else (pure ())
  writeReg GICD_TYPER (BitVec.update (← readReg GICD_TYPER) 9 (Bit 1#1))
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange (← readReg GICD_TYPER) 31 27 0b11111#5)
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange (← readReg GICD_TYPER) 18 18 1#1)
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange (← readReg GICD_TYPER) 17 17 1#1)
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange (← readReg GICD_TYPER) 16 16 1#1)
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange (← readReg GICD_TYPER) 8 8 1#1)
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange (← readReg GICD_TYPER) 10 10 1#1)
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange (← readReg GICD_TYPER) 4 0 0b00111#5)
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange (← readReg GICD_TYPER) 23 19 0b01111#5)
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMBIDR_EL1) 5 5 1#1)
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMBIDR_EL1) 4 4 0#1)
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMBIDR_EL1) 3 0 0b0000#4)
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 32 32 0#1)
  if ((← (IsFeatureImplemented FEAT_SME)) : Bool)
  then
    (do
      writeReg SMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg SMIDR_EL1) 31 24 0b01000001#8)
      writeReg SMIDR_EL1 (Sail.BitVec.updateSubrange (← readReg SMIDR_EL1) 15 15 1#1)
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 27 24 0b0001#4)
      writeReg EDDEVID1 (Sail.BitVec.updateSubrange (← readReg EDDEVID1) 7 4 0b0001#4))
  else (pure ())
  if ((HasArchVersion v9Ap3) : Bool)
  then
    (do
      if ((← (IsFeatureImplemented FEAT_MEC)) : Bool)
      then
        (do
          writeReg MECIDR_EL2 (Sail.BitVec.updateSubrange (← readReg MECIDR_EL2) 3 0 (← readReg __mecid_width))
          writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 31 28 0b0001#4))
      else (pure ()))
  else (pure ())
  if ((← (IsFeatureImplemented FEAT_SME2)) : Bool)
  then
    (do
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 27 24 0b0010#4)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 59 56 0b0001#4)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 47 44 0b0101#4)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 33 33 1#1))
  else (pure ())
  if ((HasArchVersion v8Ap8) : Bool)
  then
    (do
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 39 36 0b0010#4)
      writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR5_EL1) 3 0 0b0010#4)
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 39 36 0b0001#4)
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 31 28 0b0001#4)
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 19 16 0b0001#4)
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 23 20 0b0001#4)
      if ((← (HaveStatisticalProfiling ())) : Bool)
      then writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 35 32 0b0100#4)
      else (pure ())
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 63 60 0b0001#4)
      writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR1_EL1) 7 4 0b0001#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 3 0 0b1010#4)
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 3 0 0b1010#4)
      if ((←((pure (! (HaveEL EL3))) <&&> (do
           (pure ((_get_SCR_Type_NS (← readReg SCR)) == 1#1))))) : Bool)
      then writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 7 4 0b0000#4)
      else writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 7 4 (_get_ID_DFR0_EL1_Type_CopDbg (← readReg ID_DFR0_EL1)))
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 55 52 0b0001#4)
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 55 52 0b0001#4)
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 59 56 0b0001#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 11 8 0b1000#4)
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 27 24 0b1000#4))
  else (pure ())
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 27 24 0b0001#4)
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 19 16 0b0001#4)
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 15 12 0b0001#4)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 18 18 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 17 17 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 16 16 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 15 15 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 14 14 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 13 13 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 12 12 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 11 11 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 10 10 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 9 9 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 8 8 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 7 7 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 3 3 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 2 2 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 1 1 0#1)
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange (← readReg SCR_EL3) 0 0 0#1)
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange (← readReg CPTR_EL2) 31 31 0#1)
  writeReg CPTR_EL2 (BitVec.update (← readReg CPTR_EL2)
    (← (do
      if ((←((IsFeatureImplemented FEAT_VHE) <&&> (do
           (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))) : Bool)
      then (pure 28)
      else (pure 20))) (Bit 0#1))
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 49 49 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 52 52 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 50 50 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 44 44 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 43 43 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 42 42 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 41 41 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 40 40 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 38 38 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 37 37 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 36 36 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 33 33 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 32 32 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 31 31 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 30 30 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 29 29 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 28 28 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 27 27 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 26 26 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 25 25 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 24 24 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 23 23 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 22 22 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 21 21 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 20 20 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 19 19 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 18 18 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 17 17 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 16 16 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 15 15 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 14 14 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 13 13 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 12 12 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 11 10 0b00#2)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 9 9 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 8 8 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 7 7 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 6 6 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 5 5 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 4 4 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 3 3 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 2 2 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 1 1 0#1)
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 0 0 0#1)
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange (← readReg HSTR_EL2) 15 0 (Zeros (n := 16)))
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 31 31 0#1)
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 30 30 0#1)
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 27 27 0#1)
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 25 25 0#1)
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 13 13 0#1)
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 31 31 0#1)
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 30 30 0#1)
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 27 27 0#1)
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 25 25 0#1)
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 13 13 0#1)
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange (← readReg CPACR_EL1) 28 28 0#1)
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange (← readReg CPACR_EL1) 21 20 0b00#2)
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL1) 31 31 0#1)
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL1) 30 30 0#1)
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL1) 27 27 0#1)
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL1) 25 25 0#1)
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL1) 13 13 0#1)
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL3) 31 31 0#1)
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL3) 30 30 0#1)
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL3) 27 27 0#1)
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL3) 25 25 0#1)
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL3) 13 13 0#1)
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSIDR_EL1) 24 24 1#1)
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSIDR_EL1) 6 6 1#1)
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSIDR_EL1) 19 16 0b0011#4)
  match SPEMaxRecordSize with
  | 64 => writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSIDR_EL1) 15 12 0b0110#4)
  | _ => (Unreachable ())
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSIDR_EL1) 3 3 1#1)
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSIDR_EL1) 2 2 1#1)
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSIDR_EL1) 1 1 1#1)
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg PMSIDR_EL1) 0 0 1#1)
  if ((← (EL2Enabled ())) : Bool)
  then
    (do
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange (← readReg MDCR_EL2) 14 14 0#1)
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange (← readReg MDCR_EL2) 13 12 0b10#2))
  else (pure ())
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange (← readReg MDCR_EL2) 4 0 (_get_PMCR_EL0_Type_N (← readReg PMCR_EL0)))
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange (← readReg ICC_SRE_EL3) 0 0 1#1)
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange (← readReg ICC_SRE_EL3) 3 3 1#1)
  writeReg ICC_SRE_EL1_S (Sail.BitVec.updateSubrange (← readReg ICC_SRE_EL1_S) 0 0 1#1)
  writeReg ICC_SRE_EL1_NS (Sail.BitVec.updateSubrange (← readReg ICC_SRE_EL1_NS) 0 0 1#1)
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange (← readReg ICC_SRE_EL2) 0 0 1#1)
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange (← readReg CTR_EL0) 27 24 0b0100#4)
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange (← readReg CTR_EL0) 23 20 (← readReg __exclusive_granule_size))
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange (← readReg CTR_EL0) 19 16 0b0100#4)
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange (← readReg CTR_EL0) 15 14 0b10#2)
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange (← readReg CTR_EL0) 3 0 0b0100#4)
  if ((← (HaveMTE2Ext ())) : Bool)
  then writeReg CTR_EL0 (Sail.BitVec.updateSubrange (← readReg CTR_EL0) 37 32 0b000100#6)
  else (pure ())
  if ((← (HaveMTE2Ext ())) : Bool)
  then writeReg GMID_EL1 (Sail.BitVec.updateSubrange (← readReg GMID_EL1) 3 0 (integer_subrange (← readReg __gmid_log2_block_size) 3 0))
  else (pure ())
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 23 21 0b010#3)
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 20 18 0b011#3)
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_ExtRange (← (ICC_CTLR_EL1_read ())) 1#1))
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_PRIbits (← (ICC_CTLR_EL1_read ())) 0b100#3))
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_A3V (← (ICC_CTLR_EL1_read ())) 1#1))
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_IDbits (← (ICC_CTLR_EL1_read ())) 0b001#3))
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_CTLR_EL1) 19 19 1#1)
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_CTLR_EL1) 10 8 0b100#3)
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_CTLR_EL1) 13 11 0b001#3)
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_CTLR_EL1) 15 15 1#1)
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VTR_EL2) 31 29 0b100#3)
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VTR_EL2) 28 26 0b100#3)
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VTR_EL2) 25 23 0b001#3)
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VTR_EL2) 21 21 1#1)
  writeReg CCSIDR_EL1 (Mk_CCSIDR_EL1_Type
    (set_slice 24 (← readReg CCSIDR_EL1)
      (← (do
        if ((← (IsFeatureImplemented FEAT_CCIDX)) : Bool)
        then (pure 32)
        else (pure 13))) (Sail.BitVec.zeroExtend 0xFF#8 24)))
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg CCSIDR_EL1) 23 3 (Sail.BitVec.zeroExtend 0x1#4 21))
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg CCSIDR_EL1) 2 0 0b010#3)
  writeReg CCSIDR2_EL1 (Sail.BitVec.updateSubrange (← readReg CCSIDR2_EL1) 23 0 (Sail.BitVec.zeroExtend 0xFF#8 24))
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR1_EL1) 3 0 0b0000#4)
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR1_EL1) 7 4 0b0000#4)
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR1_EL1) 15 12 0b0000#4)
  writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 3 3 (Sail.BitVec.extractLsb 0b10#2 1 1))
  writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 0 0 (Sail.BitVec.extractLsb 0b10#2 0 0))
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange (← readReg MDRAR_EL1) 1 0 0b11#2)
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange (← readReg MDRAR_EL1) 55 12 (Sail.BitVec.zeroExtend 0x22000#20 44))
  writeReg EDDFR (Sail.BitVec.updateSubrange (← readReg EDDFR) 11 8 (_get_ID_AA64DFR0_EL1_Type_PMUVer (← readReg ID_AA64DFR0_EL1)))
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange (← readReg EDDEVARCH) 11 0 0xA15#12)
  writeReg EDDEVID1 (Sail.BitVec.updateSubrange (← readReg EDDEVID1) 7 4 0b0010#4)
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange (← readReg EDDEVARCH) 15 12 0b1011#4)
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange (← readReg EDDEVARCH) 20 20 1#1)
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange (← readReg EDDEVARCH) 31 21 0b01000111011#11)
  writeReg EDDEVID (Sail.BitVec.updateSubrange (← readReg EDDEVID) 27 24 0b0001#4)
  writeReg EDDEVTYPE (Sail.BitVec.updateSubrange (← readReg EDDEVTYPE) 3 0 0b0101#4)
  writeReg EDDEVTYPE (Sail.BitVec.updateSubrange (← readReg EDDEVTYPE) 7 4 0b0001#4)
  writeReg EDPIDR0 (Sail.BitVec.updateSubrange (← readReg EDPIDR0) 7 0 (Sail.BitVec.zeroExtend 0xF#4 8))
  writeReg EDPIDR1 (Sail.BitVec.updateSubrange (← readReg EDPIDR1) 3 0 0xD#4)
  writeReg EDPIDR1 (Sail.BitVec.updateSubrange (← readReg EDPIDR1) 7 4 (Sail.BitVec.truncate 0x0B#8 4))
  writeReg EDPIDR2 (Sail.BitVec.updateSubrange (← readReg EDPIDR2) 2 0 0b011#3)
  writeReg EDPIDR2 (Sail.BitVec.updateSubrange (← readReg EDPIDR2) 3 3 1#1)
  writeReg EDCIDR0 (Sail.BitVec.updateSubrange (← readReg EDCIDR0) 7 0 0x0D#8)
  writeReg EDCIDR1 (Sail.BitVec.updateSubrange (← readReg EDCIDR1) 7 4 0b1001#4)
  writeReg EDCIDR2 (Sail.BitVec.updateSubrange (← readReg EDCIDR2) 7 0 0x05#8)
  writeReg EDCIDR3 (Sail.BitVec.updateSubrange (← readReg EDCIDR3) 7 0 0xB1#8)
  writeReg EDDFR (Sail.BitVec.updateSubrange (← readReg EDDFR) 7 4 (_get_ID_AA64DFR0_EL1_Type_TraceVer (← readReg ID_AA64DFR0_EL1)))
  writeReg EDDFR (Sail.BitVec.updateSubrange (← readReg EDDFR) 15 12 (_get_ID_AA64DFR0_EL1_Type_BRPs (← readReg ID_AA64DFR0_EL1)))
  writeReg EDDFR (Sail.BitVec.updateSubrange (← readReg EDDFR) 23 20 (_get_ID_AA64DFR0_EL1_Type_WRPs (← readReg ID_AA64DFR0_EL1)))
  writeReg EDDFR (Sail.BitVec.updateSubrange (← readReg EDDFR) 31 28 (_get_ID_AA64DFR0_EL1_Type_CTX_CMPs (← readReg ID_AA64DFR0_EL1)))
  writeReg EDDFR (Sail.BitVec.updateSubrange (← readReg EDDFR) 43 40 (_get_ID_AA64DFR0_EL1_Type_TraceFilt (← readReg ID_AA64DFR0_EL1)))
  writeReg EDPRSR (Sail.BitVec.updateSubrange (← readReg EDPRSR) 0 0 1#1)
  writeReg EDPFR (Sail.BitVec.updateSubrange (← readReg EDPFR) 3 0 (_get_ID_AA64PFR0_EL1_Type_EL0 (← readReg ID_AA64PFR0_EL1)))
  writeReg EDPFR (Sail.BitVec.updateSubrange (← readReg EDPFR) 7 4 (_get_ID_AA64PFR0_EL1_Type_EL1 (← readReg ID_AA64PFR0_EL1)))
  writeReg EDPFR (Sail.BitVec.updateSubrange (← readReg EDPFR) 11 8 (_get_ID_AA64PFR0_EL1_Type_EL2 (← readReg ID_AA64PFR0_EL1)))
  writeReg EDPFR (Sail.BitVec.updateSubrange (← readReg EDPFR) 15 12 (_get_ID_AA64PFR0_EL1_Type_EL3 (← readReg ID_AA64PFR0_EL1)))
  writeReg EDPFR (Sail.BitVec.updateSubrange (← readReg EDPFR) 23 20 (_get_ID_AA64PFR0_EL1_Type_AdvSIMD (← readReg ID_AA64PFR0_EL1)))
  writeReg EDPFR (Sail.BitVec.updateSubrange (← readReg EDPFR) 27 24 (_get_ID_AA64PFR0_EL1_Type_GIC (← readReg ID_AA64PFR0_EL1)))
  writeReg CTIDEVID (Sail.BitVec.updateSubrange (← readReg CTIDEVID) 13 8 0b100000#6)
  writeReg CTIDEVID (Sail.BitVec.updateSubrange (← readReg CTIDEVID) 21 16 0b100000#6)
  writeReg CTIDEVID (Sail.BitVec.updateSubrange (← readReg CTIDEVID) 25 24 0b01#2)
  writeReg CTIDEVARCH (Sail.BitVec.updateSubrange (← readReg CTIDEVARCH) 31 21 0b01000111011#11)
  writeReg CTIDEVARCH (Sail.BitVec.updateSubrange (← readReg CTIDEVARCH) 20 20 1#1)
  writeReg CTIDEVARCH (Sail.BitVec.updateSubrange (← readReg CTIDEVARCH) 15 0 0b0001101000010100#16)
  writeReg CTIDEVTYPE (Sail.BitVec.updateSubrange (← readReg CTIDEVTYPE) 7 4 0b0001#4)
  writeReg CTIDEVTYPE (Sail.BitVec.updateSubrange (← readReg CTIDEVTYPE) 3 0 0b0100#4)
  writeReg CTIPIDR4 (Sail.BitVec.updateSubrange (← readReg CTIPIDR4) 7 4 0b0000#4)
  writeReg CTIPIDR4 (Sail.BitVec.updateSubrange (← readReg CTIPIDR4) 3 0 0b0100#4)
  writeReg CTIPIDR2 (Sail.BitVec.updateSubrange (← readReg CTIPIDR2) 3 3 1#1)
  writeReg CTIPIDR2 (Sail.BitVec.updateSubrange (← readReg CTIPIDR2) 2 0 0b011#3)
  writeReg CTIPIDR1 (Sail.BitVec.updateSubrange (← readReg CTIPIDR1) 7 4 0b1011#4)
  writeReg CTIPIDR1 (Sail.BitVec.updateSubrange (← readReg CTIPIDR1) 3 0 0b1101#4)
  writeReg CTIPIDR0 (Sail.BitVec.updateSubrange (← readReg CTIPIDR0) 7 0 0b00001111#8)
  writeReg CTICIDR3 (Sail.BitVec.updateSubrange (← readReg CTICIDR3) 7 0 0b10110001#8)
  writeReg CTICIDR2 (Sail.BitVec.updateSubrange (← readReg CTICIDR2) 7 0 0b00000101#8)
  writeReg CTICIDR1 (Sail.BitVec.updateSubrange (← readReg CTICIDR1) 7 4 0b1001#4)
  writeReg CTICIDR1 (Sail.BitVec.updateSubrange (← readReg CTICIDR1) 3 0 0b0000#4)
  writeReg CTICIDR0 (Sail.BitVec.updateSubrange (← readReg CTICIDR0) 7 0 0b00001101#8)
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VTR_EL2) 28 26 (integer_subrange ((← readReg NUM_GIC_PREEMPTION_BITS) -i 1) 2 0))
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VTR_EL2) 4 0 (integer_subrange ((← readReg NUM_GIC_LIST_REGS) -i 1) 4 0))
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VTR_EL2) 31 29 (integer_subrange ((← readReg NUM_GIC_PRIORITY_BITS) -i 1) 2 0))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 0 0
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 0)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 1 1
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 1)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 2 2
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 2)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 3 3
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 3)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 4 4
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 4)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 5 5
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 5)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 6 6
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 6)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 7 7
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 7)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 8 8
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 8)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 9 9
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 9)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 10 10
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 10)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 11 11
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 11)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 12 12
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 12)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 13 13
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 13)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 14 14
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 14)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 15 15
    (← (do
      if ((← (IsG1ActivityMonitorImplemented 15)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 16 16
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 0)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 17 17
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 1)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 18 18
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 2)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 19 19
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 3)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 20 20
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 4)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 21 21
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 5)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 22 22
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 6)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 23 23
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 7)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 24 24
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 8)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 25 25
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 9)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 26 26
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 10)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 27 27
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 11)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 28 28
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 12)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 29 29
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 13)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 30 30
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 14)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCG1IDR_EL0) 31 31
    (← (do
      if ((← (IsG1ActivityMonitorOffsetImplemented 15)) : Bool)
      then (pure 1#1)
      else (pure 0#1))))
  if ((HasArchVersion v9Ap4) : Bool)
  then
    (do
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR1_EL1) 63 56 0x3F#8)
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR1_EL1) 43 40 0b0001#4)
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 35 32 0b0001#4)
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 39 36 0b0001#4)
      if ((← (HaveLSE128 ())) : Bool)
      then writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR0_EL1) 23 20 0b0011#4)
      else (pure ())
      if ((← (HaveGCS ())) : Bool)
      then writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 47 44 0b0001#4)
      else (pure ())
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 3 0 0b0010#4)
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR1_EL1) 47 44 0b0001#4)
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 59 56 0b0010#4)
      if ((←((HaveSVE2p1 ()) <||> (do
           (HaveSME2p1 ())))) : Bool)
      then
        (do
          writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 43 43 1#1)
          writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 27 24 0b0001#4))
      else (pure ())
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64SMFR0_EL1) 42 42 1#1)
      writeReg PMDEVID (Sail.BitVec.updateSubrange (← readReg PMDEVID) 7 4 0b0001#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 27 24 0b0001#4)
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 11 8 0b0011#4)
      if ((← (HaveFeatEBEP ())) : Bool)
      then writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR1_EL1) 51 48 0b0001#4)
      else (pure ())
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR2_EL1) 19 16 0b0010#4)
      writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 3 0 0b0111#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 35 32 0b0001#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 39 36 0b0001#4)
      writeReg EDDEVID1 (Sail.BitVec.updateSubrange (← readReg EDDEVID1) 7 4 0b0010#4)
      if ((← (HaveMTEPermExt ())) : Bool)
      then writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR2_EL1) 3 0 0b0001#4)
      else (pure ())
      if ((← (HavePFAR ())) : Bool)
      then writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 63 60 0b0001#4)
      else (pure ())
      if ((← (HaveDoubleFault2Ext ())) : Bool)
      then writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 59 56 0b0001#4)
      else (pure ())
      if ((← (HaveTHExt ())) : Bool)
      then writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 51 48 0b0001#4)
      else (pure ())
      if ((← (HaveMTE4Ext ())) : Bool)
      then
        (do
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 55 52 0b0001#4)
          writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR2_EL1) 7 4 0b0001#4)
          writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR2_EL1) 11 8 0b0001#4))
      else (pure ())
      writeReg ID_AA64MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR4_EL1) 7 4 0b0001#4)
      if ((← (HaveRASv2Ext ())) : Bool)
      then
        (do
          writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 31 28 0b0011#4)
          writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR0_EL1) 31 28 0b0011#4))
      else (pure ())
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 43 40 0b0010#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 47 44 0b0010#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 55 52 0b0010#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 59 56 0b0010#4)
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR1_EL1) 39 36 0b0001#4)
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR1_EL1) 35 32 0b0001#4)
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR1_EL1) 31 24 0x3F#8)
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR1_EL1) 23 16 0x3F#8)
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR1_EL1) 15 8 0x3F#8)
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR1_EL1) 7 0 0x1F#8)
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR1_EL1) 55 52 0b0001#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 47 44 0b0010#4)
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ZFR0_EL1) 23 20 0b0010#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 43 40 0b0010#4)
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR1_EL1) 23 20 0b0011#4)
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 31 28 0b0001#4)
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 55 52 0b0001#4)
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 51 48 0b0001#4)
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64ISAR2_EL1) 43 40 0b0001#4)
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 3 0 0b0011#4)
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 59 56 0b0011#4)
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR1_EL1) 63 60 0b0001#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 3 0 0b0001#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 11 8 0b0001#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 19 16 0b0001#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 15 12 0b0001#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 23 20 0b0001#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 27 24 0b0001#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 7 4 0b0001#4)
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR3_EL1) 63 60 0b0001#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 3 0 0b1011#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 11 8 0b1001#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 35 32 0b0101#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 59 56 0b0001#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 19 16 0b0001#4)
      writeReg PMDEVID (Sail.BitVec.updateSubrange (← readReg PMDEVID) 3 0 0b0010#4)
      writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange (← readReg PMMIR_EL1) 27 24 0b0001#4)
      writeReg PMCFGR (BitVec.update (← readReg PMCFGR) 22 (Bit 1#1))
      writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64MMFR0_EL1) 59 56 0b0010#4)
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 7 4 0b1011#4)
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 3 0 0b1011#4)
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 27 24 0b1001#4)
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR6_EL1) 19 16 0b0010#4)
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR6_EL1) 31 28 0b0001#4)
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 23 20
        (← (do
          if (((← readReg NUM_WATCHPOINTS) ≥b 16) : Bool)
          then (pure 0b1111#4)
          else (pure (integer_subrange ((← readReg NUM_WATCHPOINTS) -i 1) 3 0)))))
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64DFR0_EL1) 15 12
        (← (do
          if (((← readReg NUM_BREAKPOINTS) ≥b 16) : Bool)
          then (pure 0b1111#4)
          else (pure (integer_subrange ((← readReg NUM_BREAKPOINTS) -i 1) 3 0))))))
  else (pure ())


