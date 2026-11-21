import Armv9.Prelude
import Armv9.V8Base
import Armv9Core.Interrupts

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

def TakeUnmaskedSErrorInterrupts (_ : Unit) : SailM Unit := do
  let interrupt_req ← (( do (undefined_InterruptReq ()) ) : SailM InterruptReq )
  let interrupt_req : InterruptReq := { interrupt_req with take_SE := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_vSE := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_FIQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_vFIQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_IRQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_vIRQ := false }
  let interrupt_req : InterruptReq := { interrupt_req with iesb_req := false }
  let interrupt_req : InterruptReq := { interrupt_req with take_SE := true }
  let interrupt_req : InterruptReq := { interrupt_req with take_vSE := true }
  let interrupt_taken ← (( do (TakePendingInterrupts interrupt_req) ) : SailM Bool )
  (pure ())

