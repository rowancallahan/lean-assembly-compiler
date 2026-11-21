import Armv9.Flow
import Armv9.Arith
import Armv9.Prelude
import Armv9Core.Devices
import Armv9Core.Instrs64
import Armv9Core.Interrupts
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

def __FetchInstr (pc : (BitVec 64)) : SailM (__InstrEnc × (BitVec 32)) := do
  let hw1 ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  let hw2 ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  let isT16 ← (( do (undefined_bool ()) ) : SailM Bool )
  let enc ← (( do (undefined___InstrEnc ()) ) : SailM __InstrEnc )
  let instr ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let accdesc ← (( do (CreateAccDescIFetch ()) ) : SailM AccessDescriptor )
  (SetBTypeCompatible false)
  (CheckSoftwareStep ())
  let (enc, instr) ← (( do
    if (((← readReg PSTATE).nRW == 0#1) : Bool)
    then
      (do
        (AArch64_CheckPCAlignment ())
        let enc : __InstrEnc := __A64
        let instr ← (AArch64_MemSingle_read (← (PC_read ())) 4 accdesc true)
        (AArch64_CheckIllegalState ())
        (pure (enc, instr)))
    else
      (do
        (AArch32_CheckPCAlignment ())
        let (enc, instr) ← (( do
          if (((← readReg PSTATE).T == 1#1) : Bool)
          then
            (do
              let hw1 ← (( do (AArch32_MemSingle_read (Sail.BitVec.extractLsb pc 31 0) 2 accdesc true) ) : SailM (BitVec 16) )
              let isT16 : Bool := ((BitVec.toNat (Sail.BitVec.extractLsb hw1 15 11)) <b (BitVec.toNat 0b11101#5))
              let (enc, instr) ← (( do
                if (isT16 : Bool)
                then
                  (let enc : __InstrEnc := __T16
                  let instr : (BitVec 32) := ((Zeros (n := 16)) +++ hw1)
                  (pure (enc, instr)))
                else
                  (do
                    let hw2 ← (( do (AArch32_MemSingle_read (BitVec.addInt (Sail.BitVec.extractLsb pc 31 0) 2) 2 accdesc true) ) : SailM (BitVec 16) )
                    let enc : __InstrEnc := __T32
                    let instr : (BitVec 32) := (hw1 +++ hw2)
                    (pure (enc, instr))) ) : SailM (__InstrEnc × (BitVec 32)) )
              (pure (enc, instr)))
          else
            (do
              let enc : __InstrEnc := __A32
              let instr ← (AArch32_MemSingle_read (Sail.BitVec.extractLsb pc 31 0) 4 accdesc true)
              (pure (enc, instr))) ) : SailM (__InstrEnc × (BitVec 32)) )
        (AArch32_CheckIllegalState ())
        (pure (enc, instr))) ) : SailM (__InstrEnc × (BitVec 32)) )
  (pure (enc, instr))

def __EndCycle (_ : Unit) : SailM Unit := do
  writeReg __cycle_count ((← readReg __cycle_count) +i 1)

def __CycleEnd (_ : Unit) : SailM Unit := do
  (SPECycle ())
  (__UpdateSystemCounter ())
  if ((← (UsingAArch32 ())) : Bool)
  then (AArch32_PMUCycle ())
  else (AArch64_PMUCycle ())
  (__EndCycle ())

