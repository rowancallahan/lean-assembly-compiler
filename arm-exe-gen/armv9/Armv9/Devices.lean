import Armv9.V8Base

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

def __GIC_ClearPendingInterrupt (intid : (BitVec 32)) : SailM Unit := do
  match (← readReg __GIC_Pending) with
  | .some pending_intid =>
    (do
      if (((__GIC_InterruptID pending_intid) == intid) : Bool)
      then writeReg __GIC_Pending none
      else (pure ()))
  | _ => (pure ())

def gic_write_ram (offset : (BitVec 16)) (data : (BitVec 32)) : SailM Unit := do
  let accdesc ← do (CreateAccDescGPR MemOp_STORE false true false)
  let pa := (Sail.BitVec.zeroExtend (GIC_BASE +++ offset) 56)
  match (← (sail_mem_write (write_request accdesc none 4 (Sail.BitVec.zeroExtend pa 64) pa data))) with
  | .Ok _ => (pure ())
  | .Err _ => sail_assert false "src/devices.sail:145.26-145.27"

def Init_Devices (_ : Unit) : SailM Unit := do
  writeReg __GIC_Pending none
  writeReg __GIC_Active none

def __UpdateSystemCounter (_ : Unit) : SailM Unit := do
  (GenericCounterTick ())

def __HandlePendingInterrupt (_ : Unit) : SailM Unit := do
  match (← readReg __GIC_Pending) with
  | .some intid =>
    (do
      let _ : Unit := (prerr_bits "[Clock] GIC interrupt " (__GIC_InterruptID intid))
      (AArch64_TakePhysicalIRQException ()))
  | none => (pure ())

