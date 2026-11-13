import Armv9.Flow
import Armv9.Arith
import Armv9.Prelude
import Armv9.V8Base
import Armv9.Interrupts
import Armv9.Devices
import Armv9.DecodeEnd

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

def UnallocatedA32_Instruction (instr : (BitVec 32)) : SailM Unit := do
  let nop ← (( do (undefined_bool ()) ) : SailM Bool )
  let nop : Bool :=
    let b__0 := instr
    if (((Sail.BitVec.extractLsb b__0 27 16) == (0x320#12 : (BitVec 12))) : Bool)
    then
      (let cond : (BitVec 4) := (Sail.BitVec.extractLsb instr 31 28)
      (cond != 0b1111#4))
    else
      (if ((((Sail.BitVec.extractLsb b__0 31 24) == (0xF4#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb b__0 22 20) == (0b001#3 : (BitVec 3)))) : Bool)
      then true
      else
        (if ((((Sail.BitVec.extractLsb b__0 31 24) == (0xF6#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb b__0 22 20) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))))) : Bool)
        then true
        else false))
  if ((←((pure (! nop)) <&&> (do
       (ConditionHolds (← (AArch32_CurrentCond ())))))) : Bool)
  then (AArch32_UndefinedFault ())
  else (pure ())

def UnallocatedT32_32_Instruction (instr : (BitVec 32)) : SailM Unit := do
  let nop ← (( do (undefined_bool ()) ) : SailM Bool )
  let nop : Bool :=
    let b__0 := instr
    if ((((Sail.BitVec.extractLsb b__0 31 20) == (0xF3A#12 : (BitVec 12))) && (((Sail.BitVec.extractLsb b__0 15 14) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb b__0 12 12) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 10 8) == (0b000#3 : (BitVec 3)))))) : Bool)
    then true
    else
      (if ((((Sail.BitVec.extractLsb b__0 31 20) == (0xF93#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb b__0 15 6) == (0b1111000000#10 : (BitVec 10)))) : Bool)
      then true
      else
        (if ((((Sail.BitVec.extractLsb b__0 31 20) == (0xF93#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb b__0 15 8) == (0xFC#8 : (BitVec 8)))) : Bool)
        then true
        else
          (if ((((Sail.BitVec.extractLsb b__0 31 20) == (0xF9B#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb b__0 15 12) == (0xF#4 : (BitVec 4)))) : Bool)
          then true
          else
            (if ((((Sail.BitVec.extractLsb b__0 31 24) == (0xF9#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb b__0 22 12) == (0b01111111111#11 : (BitVec 11)))) : Bool)
            then true
            else false))))
  let nop := nop
  if ((←((pure (! nop)) <&&> (do
       (ConditionHolds (← (AArch32_CurrentCond ())))))) : Bool)
  then (AArch32_UndefinedFault ())
  else (pure ())

def UnallocatedT32_16_Instruction (instr : (BitVec 16)) : SailM Unit := do
  let nop ← (( do (undefined_bool ()) ) : SailM Bool )
  let nop : Bool :=
    let b__0 := instr
    if ((((Sail.BitVec.extractLsb b__0 15 8) == (0xBF#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb b__0 3 0) == (0x0#4 : (BitVec 4)))) : Bool)
    then
      (let hint : (BitVec 4) := (Sail.BitVec.extractLsb instr 7 4)
      let b__1 := hint
      if (((Sail.BitVec.extractLsb b__1 3 1) == (0b011#3 : (BitVec 3))) : Bool)
      then true
      else
        (if (((Sail.BitVec.extractLsb b__1 3 3) == (1#1 : (BitVec 1))) : Bool)
        then true
        else false))
    else false
  if ((←((pure (! nop)) <&&> (do
       (ConditionHolds (← (AArch32_CurrentCond ())))))) : Bool)
  then (AArch32_UndefinedFault ())
  else (pure ())

def __DefaultCond (enc : __InstrEnc) : SailM (BitVec 4) := do
  let cond ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  if ((←((pure ((BEq.beq enc __A64) || (BEq.beq enc __A32))) <||> (do
       (pure ((Sail.BitVec.extractLsb (← readReg PSTATE).IT 3 0) == (Zeros (n := 4))))))) : Bool)
  then (pure 0xE#4)
  else (do (pure (Sail.BitVec.extractLsb (← readReg PSTATE).IT 7 4)))

def __SetThisInstrDetails (enc : __InstrEnc) (opcode : (BitVec 32)) (cond : (BitVec 4)) : SailM Unit := do
  writeReg __ThisInstrEnc enc
  writeReg __ThisInstr opcode
  writeReg __currentCond cond

def ExecuteA64 (instr : (BitVec 32)) : SailM Unit := do
  if ((← (Halted ())) : Bool)
  then
    sailTryCatch ((do
        (__SetThisInstrDetails __A64 instr (← (__DefaultCond __A64)))
        (__DecodeA64 (BitVec.toNat (← readReg _PC)) instr))) (fun the_exception => 
      match the_exception with
        | exn =>
          (do
            if ((IsExceptionTaken exn) : Bool)
            then (pure ())
            else
              (do
                if ((((IsSEE exn) || (IsUNDEFINED exn)) || (IsUNPREDICTABLE exn)) : Bool)
                then (AArch64_UndefinedFault ())
                else sailThrow (exn))))
  else (__DecodeA64 (BitVec.toNat (← readReg _PC)) instr)

def ExecuteA32 (instr : (BitVec 32)) : SailM Unit := do
  (__DecodeA32 (BitVec.toNat (← readReg _PC)) instr)

def ExecuteT32__1 (instr : (BitVec 32)) : SailM Unit := do
  if ((← (Halted ())) : Bool)
  then
    sailTryCatch ((do
        (__SetThisInstrDetails __T32 instr (← (__DefaultCond __T32)))
        (__DecodeT32 (BitVec.toNat (← readReg _PC)) instr))) (fun the_exception => 
      match the_exception with
        | exn =>
          (do
            if ((IsExceptionTaken exn) : Bool)
            then (pure ())
            else
              (do
                if ((((IsSEE exn) || (IsUNDEFINED exn)) || (IsUNPREDICTABLE exn)) : Bool)
                then (UnallocatedT32_32_Instruction instr)
                else sailThrow (exn))))
  else (__DecodeT32 (BitVec.toNat (← readReg _PC)) instr)

def ExecuteT16 (instr : (BitVec 16)) : SailM Unit := do
  (__DecodeT16 (BitVec.toNat (← readReg _PC)) instr)

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

def __TryDecodeExecute (enc : __InstrEnc) (instr : (BitVec 32)) : SailM Unit := do
  match enc with
  | .__A64 => (ExecuteA64 instr)
  | .__A32 => (ExecuteA32 instr)
  | .__T16 => (ExecuteT16 (Sail.BitVec.extractLsb instr 15 0))
  | .__T32 => (ExecuteT32__1 instr)

def __DecodeExecute (enc : __InstrEnc) (instr : (BitVec 32)) : SailM Unit := do
  sailTryCatch ((__TryDecodeExecute enc instr)) (fun the_exception => 
    match the_exception with
      | exn =>
        (do
          if ((IsSEE exn) : Bool)
          then (__TryDecodeExecute enc instr)
          else sailThrow (exn)))

def __CheckForEmulatorTermination (enc : __InstrEnc) (instr : (BitVec 32)) : SailM Unit := do
  match (← readReg __emulator_termination_opcode) with
  | .some magic =>
    (do
      if ((instr == magic) : Bool)
      then
        (do
          let _ : Unit := (print (String.append (String.append "[Sail] Terminating emulation at opcode " (BitVec.toFormatted magic)) "
"))
          throw Error.Exit)
      else (pure ()))
  | none => (pure ())

def __InstructionExecute (_ : Unit) : SailM Unit := do
  let enc ← (( do (undefined___InstrEnc ()) ) : SailM __InstrEnc )
  let instr ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_PipeAdv (← (EDSCR_read ())) 1#1))
  if ((! (IsZero (← readReg EDESR))) : Bool)
  then
    (do
      (CheckPendingOSUnlockCatch ())
      (CheckPendingResetCatch ())
      (CheckPendingExceptionCatch true))
  else (pure ())
  sailTryCatch ((do
      writeReg ShouldAdvanceIT (←((pure ((← readReg PSTATE).nRW == 1#1)) <&&> (do
        (pure ((← readReg PSTATE).T == 1#1)))))
      writeReg ShouldAdvanceSS true
      let pc ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
      let (enc, instr) ← (( do
        let (tup__0, tup__1) ← do (__FetchInstr pc)
        let enc : __InstrEnc := tup__0
        let instr : (BitVec 32) := tup__1
        (pure (enc, instr)) ) : SailM (__InstrEnc × (BitVec 32)) )
      (__CheckForEmulatorTermination enc instr)
      (PMUEvent PMU_EVENT_INST_SPEC)
      writeReg __BranchTaken false
      writeReg __ExclusiveMonitorSet false
      (__SetThisInstrDetails enc instr (← (__DefaultCond enc)))
      (SPEPreExecution ())
      (__DecodeExecute enc instr)
      (PMUEvent PMU_EVENT_INST_RETIRED))) (fun the_exception => 
    match the_exception with
      | exn =>
        (do
          if ((((IsSEE exn) || (IsUNDEFINED exn)) || (IsUNPREDICTABLE exn)) : Bool)
          then
            (do
              if ((← (UsingAArch32 ())) : Bool)
              then
                (do
                  match enc with
                  | .__A32 => (UnallocatedA32_Instruction instr)
                  | .__T16 => (UnallocatedT32_16_Instruction (Sail.BitVec.extractLsb instr 15 0))
                  | .__T32 => (UnallocatedT32_32_Instruction instr)
                  | _ => (Unreachable ()))
              else (AArch64_UndefinedFault ()))
          else
            (do
              if ((IsExceptionTaken exn) : Bool)
              then (pure ())
              else sailThrow (exn))))
  (SPEPostExecution ())
  writeReg InGuardedPage false
  if ((! (← (AArch64_ExecutingERETInstr ()))) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with BTYPE := ← (do readReg BTypeNext) }
  else (pure ())
  if ((! (← readReg __BranchTaken)) : Bool)
  then writeReg _PC (Sail.BitVec.extractLsb (BitVec.addInt (← readReg _PC) (fdiv_int (← (ThisInstrLength ())) 8)) 63 0)
  else (pure ())
  if ((← readReg ShouldAdvanceIT) : Bool)
  then (AArch32_ITAdvance ())
  else (pure ())
  if ((← readReg ShouldAdvanceSS) : Bool)
  then (SSAdvance ())
  else (pure ())

def __TopLevel (_ : Unit) : SailM Unit := do
  let interrupt_taken ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((← (Halted ())) : Bool)
  then (pure ())
  else
    (do
      let interrupt_req ← (( do (undefined_InterruptReq ()) ) : SailM InterruptReq )
      let interrupt_req : InterruptReq := { interrupt_req with take_SE := true }
      let interrupt_req : InterruptReq := { interrupt_req with take_vSE := true }
      let interrupt_req : InterruptReq := { interrupt_req with take_IRQ := true }
      let interrupt_req : InterruptReq := { interrupt_req with take_vIRQ := true }
      let interrupt_req : InterruptReq := { interrupt_req with take_FIQ := true }
      let interrupt_req : InterruptReq := { interrupt_req with take_vFIQ := true }
      sailTryCatch ((do
          let interrupt_taken ← (( do (TakePendingInterrupts interrupt_req) ) : SailM Bool )
          if ((! interrupt_taken) : Bool)
          then
            (do
              if ((BEq.beq (← readReg Branchtypetaken) BranchType_RESET) : Bool)
              then
                (do
                  (CheckResetCatch ())
                  writeReg Branchtypetaken BranchType_UNKNOWN)
              else (pure ())
              (__InstructionExecute ()))
          else (pure ()))) (fun the_exception => 
        match the_exception with
          | .Error_SError iesb_req =>
            (do
              if ((← (UsingAArch32 ())) : Bool)
              then (AArch32_TakePhysicalSErrorException iesb_req)
              else (AArch64_TakePhysicalSErrorException iesb_req))
          | .Error_ExceptionTaken () => (pure ())
          | e => sailThrow (e)))

def __EndCycle (_ : Unit) : SailM Unit := do
  writeReg __cycle_count ((← readReg __cycle_count) +i 1)

def __CycleEnd (_ : Unit) : SailM Unit := do
  (SPECycle ())
  (__UpdateSystemCounter ())
  if ((← (UsingAArch32 ())) : Bool)
  then (AArch32_PMUCycle ())
  else (AArch64_PMUCycle ())
  (__EndCycle ())

