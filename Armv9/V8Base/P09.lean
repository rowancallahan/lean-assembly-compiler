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
import Armv9.V8Base.P06

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

/-- Type quantifiers: ec : Int -/
def AArch64_AArch32SystemAccessTrapSyndrome (instr : (BitVec 32)) (ec : Int) : SailM ExceptionRecord := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  let except ← (( do
    match ec with
    | 0 => (do (ExceptionSyndrome Exception_Uncategorized))
    | 3 => (do (ExceptionSyndrome Exception_CP15RTTrap))
    | 4 => (do (ExceptionSyndrome Exception_CP15RRTTrap))
    | 5 => (do (ExceptionSyndrome Exception_CP14RTTrap))
    | 6 => (do (ExceptionSyndrome Exception_CP14DTTrap))
    | 7 => (do (ExceptionSyndrome Exception_AdvSIMDFPAccessTrap))
    | 8 => (do (ExceptionSyndrome Exception_FPIDTrap))
    | 12 => (do (ExceptionSyndrome Exception_CP14RRTTrap))
    | _ =>
      (do
        (Unreachable ())
        (pure except)) ) : SailM ExceptionRecord )
  let iss : (BitVec 20) := (Zeros (n := 20))
  if ((BEq.beq except.exceptype Exception_Uncategorized) : Bool)
  then (pure except)
  else
    (do
      let iss ← (( do
        if (((BEq.beq except.exceptype Exception_FPIDTrap) || ((BEq.beq except.exceptype Exception_CP14RTTrap) || (BEq.beq except.exceptype Exception_CP15RTTrap))) : Bool)
        then
          (do
            let iss : (BitVec 20) :=
              if ((bne except.exceptype Exception_FPIDTrap) : Bool)
              then
                (let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 19 17 (Sail.BitVec.extractLsb instr 7 5))
                let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 16 14 (Sail.BitVec.extractLsb instr 23 21))
                let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 13 10 (Sail.BitVec.extractLsb instr 19 16))
                (Sail.BitVec.updateSubrange iss 4 1 (Sail.BitVec.extractLsb instr 3 0)))
              else
                (let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 19 17 0b000#3)
                let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 16 14 0b111#3)
                let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 13 10 (Sail.BitVec.extractLsb instr 19 16))
                (Sail.BitVec.updateSubrange iss 4 1 0b0000#4))
            if ((((BitVec.join1 [(BitVec.access instr 20)]) == 1#1) && ((Sail.BitVec.extractLsb instr 15 12) == 0b1111#4)) : Bool)
            then (pure (Sail.BitVec.updateSubrange iss 9 5 0b11111#5))
            else
              (do
                if ((((BitVec.join1 [(BitVec.access instr 20)]) == 0#1) && ((Sail.BitVec.extractLsb instr 15 12) == 0b1111#4)) : Bool)
                then (do (pure (Sail.BitVec.updateSubrange iss 9 5 (← (__UNKNOWN_bits 5)))))
                else (do (pure (Sail.BitVec.updateSubrange iss 9 5 (integer_subrange (← (LookUpRIndex (BitVec.toNat (Sail.BitVec.extractLsb instr 15 12)) (← readReg PSTATE).M)) 4 0))))))
        else
          (do
            if (((BEq.beq except.exceptype Exception_CP14RRTTrap) || ((BEq.beq except.exceptype Exception_AdvSIMDFPAccessTrap) || (BEq.beq except.exceptype Exception_CP15RRTTrap))) : Bool)
            then
              (do
                let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 19 16 (Sail.BitVec.extractLsb instr 7 4))
                let iss ← (( do
                  if (((Sail.BitVec.extractLsb instr 19 16) == 0b1111#4) : Bool)
                  then (do (pure (Sail.BitVec.updateSubrange iss 14 10 (← (__UNKNOWN_bits 5)))))
                  else (do (pure (Sail.BitVec.updateSubrange iss 14 10 (integer_subrange (← (LookUpRIndex (BitVec.toNat (Sail.BitVec.extractLsb instr 19 16)) (← readReg PSTATE).M)) 4 0)))) ) : SailM (BitVec 20) )
                let iss ← (( do
                  if (((Sail.BitVec.extractLsb instr 15 12) == 0b1111#4) : Bool)
                  then (do (pure (Sail.BitVec.updateSubrange iss 9 5 (← (__UNKNOWN_bits 5)))))
                  else (do (pure (Sail.BitVec.updateSubrange iss 9 5 (integer_subrange (← (LookUpRIndex (BitVec.toNat (Sail.BitVec.extractLsb instr 15 12)) (← readReg PSTATE).M)) 4 0)))) ) : SailM (BitVec 20) )
                (pure (Sail.BitVec.updateSubrange iss 4 1 (Sail.BitVec.extractLsb instr 3 0))))
            else
              (do
                if ((BEq.beq except.exceptype Exception_CP14DTTrap) : Bool)
                then
                  (do
                    let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 19 12 (Sail.BitVec.extractLsb instr 7 0))
                    let iss : (BitVec 20) := (BitVec.update iss 4 (Bit (BitVec.join1 [(BitVec.access instr 23)])))
                    let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 2 1 ((BitVec.join1 [(BitVec.access instr 24)]) +++ (BitVec.join1 [(BitVec.access instr 21)])))
                    if (((Sail.BitVec.extractLsb instr 19 16) == 0b1111#4) : Bool)
                    then
                      (do
                        let iss ← (pure (Sail.BitVec.updateSubrange iss 9 5 (← (__UNKNOWN_bits 5))))
                        (pure (BitVec.update iss 3 (Bit 1#1))))
                    else (pure iss))
                else (pure iss))) ) : SailM (BitVec 20) )
      let iss : (BitVec 20) := (BitVec.update iss 0 (Bit (BitVec.join1 [(BitVec.access instr 20)])))
      let except ← (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 24 20 (← (ConditionSyndrome ()))))) })
      (pure { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 0 iss) }))

def SPESampleAddContext (_ : Unit) : SailM Unit := do
  if ((← (CollectContextIDR1 ())) : Bool)
  then
    (do
      writeReg SPESampleContextEL1 (Sail.BitVec.extractLsb (← readReg CONTEXTIDR_EL1) 31 0)
      writeReg SPESampleContextEL1Valid true)
  else (pure ())
  if ((← (CollectContextIDR2 ())) : Bool)
  then
    (do
      writeReg SPESampleContextEL2 (Sail.BitVec.extractLsb (← readReg CONTEXTIDR_EL2) 31 0)
      writeReg SPESampleContextEL2Valid true)
  else (pure ())

def SPESampleAddTimeStamp (_ : Unit) : SailM Unit := do
  let timestamp ← (( do (CollectTimeStamp ()) ) : SailM TimeStamp )
  match timestamp with
  | .TimeStamp_None => writeReg SPESampleTimestampValid false
  | _ =>
    (do
      writeReg SPESampleTimestampValid true
      writeReg SPESampleTimestamp (← (GetTimestamp timestamp)))

/-- Type quantifiers: k_N : Nat, List.elem k_N [8, 16, 32, 64] -/
def SPEAddPacketToRecord (header_hi : (BitVec 2)) (header_lo : (BitVec 4)) (payload : (BitVec k_N)) : SailM Unit := do
  sail_assert ((Nat.mod (Sail.BitVec.length payload) 8) == 0) "src/v8_base.sail:35115.26-35115.27"
  let sz ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let sz ← (( do
    match (Sail.BitVec.length payload) with
    | 8 => (pure 0b00#2)
    | 16 => (pure 0b01#2)
    | 32 => (pure 0b10#2)
    | 64 => (pure 0b11#2)
    | _ =>
      (do
        (Unreachable ())
        (pure sz)) ) : SailM (BitVec 2) )
  let header : (BitVec 8) := ((header_hi +++ sz) +++ header_lo)
  (SPEAddByteToRecord header)
  let loop_i_lower := 0
  let loop_i_upper := ((Int.ediv (Sail.BitVec.length payload) 8) -i 1)
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do (SPEAddByteToRecord (Sail.BitVec.extractLsb payload ((i *i 8) +i 7) (i *i 8)))
  (pure loop_vars)

def SPEWriteToBuffer (_ : Unit) : SailM Unit := do
  sail_assert (← (ProfilingBufferEnabled ())) "src/v8_base.sail:35284.35-35284.36"
  let aligned ← (( do (pure (is_zero_subrange (_get_PMBPTR_EL1_Type_PTR (← readReg PMBPTR_EL1)) ((BitVec.toNat (_get_PMBIDR_EL1_Type_Align (← readReg PMBIDR_EL1))) -i 1) 0)) ) : SailM Bool )
  let ttw_fault_as_external_abort ← (( do (__IMPDEF_boolean "SPE TTW fault External abort") ) : SailM Bool )
  let fault ← (( do (undefined_FaultRecord ()) ) : SailM FaultRecord )
  let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
  let addrdesc ← (( do (undefined_AddressDescriptor ()) ) : SailM AddressDescriptor )
  let owning_ss ← (( do (undefined_SecurityState ()) ) : SailM SecurityState )
  let owning_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let (owning_el, owning_ss) ← (( do
    let (tup__0, tup__1) ← do (ProfilingBufferOwner ())
    let owning_ss : SecurityState := tup__0
    let owning_el : (BitVec 2) := tup__1
    (pure (owning_el, owning_ss)) ) : SailM ((BitVec 2) × SecurityState) )
  let accdesc ← (( do (CreateAccDescSPE owning_ss owning_el) ) : SailM AccessDescriptor )
  let start_vaddr ← (( do (pure (Sail.BitVec.extractLsb (← readReg PMBPTR_EL1) 63 0)) ) : SailM (BitVec 64) )
  let (addrdesc, fault, memstatus) ← (( do
    let loop_i_lower := 0
    let loop_i_upper ← do (pure ((← readReg SPERecordSize) -i 1))
    let mut loop_vars := (addrdesc, fault, memstatus)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (addrdesc, fault, memstatus) := loop_vars
      loop_vars ← do
        let (addrdesc, fault, memstatus) ← (( do
          if (((_get_PMBSR_EL1_Type_S (← readReg PMBSR_EL1)) == 0#1) : Bool)
          then
            (do
              sail_assert ((0 ≤b i) && (i <b 64)) "src/v8_base.sail:35297.60-35297.61"
              let (addrdesc, memstatus) ← (( do
                let (tup__0, tup__1) ← do (DebugMemWrite (Sail.BitVec.extractLsb (← readReg PMBPTR_EL1) 63 0) accdesc aligned (GetElem?.getElem! (← readReg SPERecordData) i))
                let memstatus : PhysMemRetStatus := tup__0
                let addrdesc : AddressDescriptor := tup__1
                (pure (addrdesc, memstatus)) ) : SailM (AddressDescriptor × PhysMemRetStatus) )
              let fault : FaultRecord := addrdesc.fault
              let ttw_fault : Bool := ((BEq.beq fault.statuscode Fault_SyncExternalOnWalk) || (BEq.beq fault.statuscode Fault_SyncParityOnWalk))
              if (((IsFault__1 fault.statuscode) && (! (ttw_fault && ttw_fault_as_external_abort))) : Bool)
              then (DebugWriteFault (Sail.BitVec.extractLsb (← readReg PMBPTR_EL1) 63 0) fault)
              else
                (do
                  if (((IsFault__2 memstatus) || (ttw_fault && ttw_fault_as_external_abort)) : Bool)
                  then (DebugWriteExternalAbort memstatus addrdesc start_vaddr)
                  else (pure ()))
              if ((IsZero (_get_PMBSR_EL1_Type_S (← readReg PMBSR_EL1))) : Bool)
              then writeReg PMBPTR_EL1 (Mk_PMBPTR_EL1_Type (BitVec.addInt (← readReg PMBPTR_EL1) 1))
              else (pure ())
              (pure (addrdesc, fault, memstatus)))
          else (pure (addrdesc, fault, memstatus)) ) : SailM (AddressDescriptor × FaultRecord × PhysMemRetStatus) )
        (pure (addrdesc, fault, memstatus))
    (pure loop_vars) ) : SailM (AddressDescriptor × FaultRecord × PhysMemRetStatus) )
  (pure ())

def AArch64_TLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2))))) "src/v8_base.sail:35915.46-35915.47"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ALL }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBI_VMALL (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:35933.65-35933.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VMALL }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBI_VMALLS12 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2))))) "src/v8_base.sail:35952.46-35952.47"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VMALLS12 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:35971.65-35971.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ASID }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:35991.65-35991.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord := { r with address := (Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb Xt 43 0) +++ (Zeros (n := 12))) 64) }
  let r : TLBIRecord := { r with d64 := true }
  let r : TLBIRecord :=
    { r with d128 := 
      (let b__0 := r.ttl
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBIP_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:36018.65-36018.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord := { r with address := (Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb Xt 107 64) +++ (Zeros (n := 12))) 64) }
  let r : TLBIRecord :=
    { r with d64 := 
      (let b__0 := r.ttl
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  let r : TLBIRecord := { r with d128 := true }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBI_VAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:36045.65-36045.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VAA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord := { r with address := (Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb Xt 43 0) +++ (Zeros (n := 12))) 64) }
  let r : TLBIRecord := { r with d64 := true }
  let r : TLBIRecord :=
    { r with d128 := 
      (let b__0 := r.ttl
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBIP_VAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:36071.65-36071.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VAA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord := { r with address := (Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb Xt 107 64) +++ (Zeros (n := 12))) 64) }
  let r : TLBIRecord :=
    { r with d64 := 
      (let b__0 := r.ttl
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  let r : TLBIRecord := { r with d128 := true }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBI_IPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2))))) "src/v8_base.sail:36097.46-36097.47"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord := { r with address := (Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb Xt 39 0) +++ (Zeros (n := 12))) 64) }
  let r : TLBIRecord := { r with d64 := true }
  let r : TLBIRecord :=
    { r with d128 := 
      (let b__0 := r.ttl
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  let r ← (( do
    match security with
    | .SS_NonSecure => (pure { r with ipaspace := PAS_NonSecure })
    | .SS_Secure =>
      (pure { r with ipaspace := 
          if (((BitVec.join1 [(BitVec.access Xt 63)]) == 1#1) : Bool)
          then PAS_NonSecure
          else PAS_Secure })
    | .SS_Realm => (pure { r with ipaspace := PAS_Realm })
    | _ =>
      (do
        (Unreachable ())
        (pure r)) ) : SailM TLBIRecord )
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBIP_IPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2))))) "src/v8_base.sail:36137.46-36137.47"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.extractLsb Xt 47 44) }
  let r : TLBIRecord := { r with address := (Sail.BitVec.zeroExtend ((Sail.BitVec.extractLsb Xt 107 64) +++ (Zeros (n := 12))) 64) }
  let r : TLBIRecord :=
    { r with d64 := 
      (let b__0 := r.ttl
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then true
      else false : Bool) }
  let r : TLBIRecord := { r with d128 := true }
  let r ← (( do
    match security with
    | .SS_NonSecure => (pure { r with ipaspace := PAS_NonSecure })
    | .SS_Secure =>
      (pure { r with ipaspace := 
          if (((BitVec.join1 [(BitVec.access Xt 63)]) == 1#1) : Bool)
          then PAS_NonSecure
          else PAS_Secure })
    | .SS_Realm => (pure { r with ipaspace := PAS_Realm })
    | _ =>
      (do
        (Unreachable ())
        (pure r)) ) : SailM TLBIRecord )
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBI_RVA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:36297.65-36297.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RVA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord := { r with d64 := true }
  let r : TLBIRecord := { r with d128 := ((Sail.BitVec.extractLsb r.ttl 1 0) == 0b00#2) }
  let valid_name ← (( do (undefined_bool ()) ) : SailM Bool )
  let (r, valid_name) ← (( do
    let (tup__0, tup__1, tup__2, tup__3) ← do (TLBIRange regime Xt)
    let valid_name : Bool := tup__0
    let r : TLBIRecord := { r with tg := tup__1 }
    let r : TLBIRecord := { r with address := tup__2 }
    let r : TLBIRecord := { r with end_address_name := tup__3 }
    (pure (r, valid_name)) ) : SailM (TLBIRecord × Bool) )
  if ((! valid_name) : Bool)
  then (pure ())
  else
    (do
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure ()))

def AArch64_TLBIP_RVA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:36325.65-36325.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RVA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord := { r with d64 := ((Sail.BitVec.extractLsb r.ttl 1 0) == 0b00#2) }
  let r : TLBIRecord := { r with d128 := true }
  let valid_name ← (( do (undefined_bool ()) ) : SailM Bool )
  let (r, valid_name) ← (( do
    let (tup__0, tup__1, tup__2, tup__3) ← do (TLBIPRange regime Xt)
    let valid_name : Bool := tup__0
    let r : TLBIRecord := { r with tg := tup__1 }
    let r : TLBIRecord := { r with address := tup__2 }
    let r : TLBIRecord := { r with end_address_name := tup__3 }
    (pure (r, valid_name)) ) : SailM (TLBIRecord × Bool) )
  if ((! valid_name) : Bool)
  then (pure ())
  else
    (do
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure ()))

def AArch64_TLBI_RVAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:36353.65-36353.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RVAA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord := { r with d64 := true }
  let r : TLBIRecord := { r with d128 := ((Sail.BitVec.extractLsb r.ttl 1 0) == 0b00#2) }
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let baseaddr := (BitVec.toInt (Sail.BitVec.extractLsb Xt 36 0))
  let valid_name ← (( do (undefined_bool ()) ) : SailM Bool )
  let (r, valid_name) ← (( do
    let (tup__0, tup__1, tup__2, tup__3) ← do (TLBIRange regime Xt)
    let valid_name : Bool := tup__0
    let r : TLBIRecord := { r with tg := tup__1 }
    let r : TLBIRecord := { r with address := tup__2 }
    let r : TLBIRecord := { r with end_address_name := tup__3 }
    (pure (r, valid_name)) ) : SailM (TLBIRecord × Bool) )
  if ((! valid_name) : Bool)
  then (pure ())
  else
    (do
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure ()))

def AArch64_TLBIP_RVAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:36384.65-36384.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RVAA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord := { r with d64 := ((Sail.BitVec.extractLsb r.ttl 1 0) == 0b00#2) }
  let r : TLBIRecord := { r with d128 := true }
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let baseaddr := (BitVec.toInt (Sail.BitVec.extractLsb Xt 36 0))
  let valid_name ← (( do (undefined_bool ()) ) : SailM Bool )
  let (r, valid_name) ← (( do
    let (tup__0, tup__1, tup__2, tup__3) ← do (TLBIPRange regime Xt)
    let valid_name : Bool := tup__0
    let r : TLBIRecord := { r with tg := tup__1 }
    let r : TLBIRecord := { r with address := tup__2 }
    let r : TLBIRecord := { r with end_address_name := tup__3 }
    (pure (r, valid_name)) ) : SailM (TLBIRecord × Bool) )
  if ((! valid_name) : Bool)
  then (pure ())
  else
    (do
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure ()))

def AArch64_TLBI_RIPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:36415.65-36415.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RIPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord := { r with d64 := true }
  let r : TLBIRecord := { r with d128 := ((Sail.BitVec.extractLsb r.ttl 1 0) == 0b00#2) }
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let baseaddr := (BitVec.toInt (Sail.BitVec.extractLsb Xt 36 0))
  let valid_name ← (( do (undefined_bool ()) ) : SailM Bool )
  let (r, valid_name) ← (( do
    let (tup__0, tup__1, tup__2, tup__3) ← do (TLBIRange regime Xt)
    let valid_name : Bool := tup__0
    let r : TLBIRecord := { r with tg := tup__1 }
    let r : TLBIRecord := { r with address := tup__2 }
    let r : TLBIRecord := { r with end_address_name := tup__3 }
    (pure (r, valid_name)) ) : SailM (TLBIRecord × Bool) )
  if ((! valid_name) : Bool)
  then (pure ())
  else
    (do
      let r ← (( do
        match security with
        | .SS_NonSecure => (pure { r with ipaspace := PAS_NonSecure })
        | .SS_Secure =>
          (pure { r with ipaspace := 
              if (((BitVec.join1 [(BitVec.access Xt 63)]) == 1#1) : Bool)
              then PAS_NonSecure
              else PAS_Secure })
        | .SS_Realm => (pure { r with ipaspace := PAS_Realm })
        | _ =>
          (do
            (Unreachable ())
            (pure r)) ) : SailM TLBIRecord )
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure ()))

def AArch64_TLBIP_RIPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:36460.65-36460.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RIPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord := { r with d64 := ((Sail.BitVec.extractLsb r.ttl 1 0) == 0b00#2) }
  let r : TLBIRecord := { r with d128 := true }
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let baseaddr := (BitVec.toInt (Sail.BitVec.extractLsb Xt 36 0))
  let valid_name ← (( do (undefined_bool ()) ) : SailM Bool )
  let (r, valid_name) ← (( do
    let (tup__0, tup__1, tup__2, tup__3) ← do (TLBIPRange regime Xt)
    let valid_name : Bool := tup__0
    let r : TLBIRecord := { r with tg := tup__1 }
    let r : TLBIRecord := { r with address := tup__2 }
    let r : TLBIRecord := { r with end_address_name := tup__3 }
    (pure (r, valid_name)) ) : SailM (TLBIRecord × Bool) )
  if ((! valid_name) : Bool)
  then (pure ())
  else
    (do
      let r ← (( do
        match security with
        | .SS_NonSecure => (pure { r with ipaspace := PAS_NonSecure })
        | .SS_Secure =>
          (pure { r with ipaspace := 
              if (((BitVec.join1 [(BitVec.access Xt 63)]) == 1#1) : Bool)
              then PAS_NonSecure
              else PAS_Secure })
        | .SS_Realm => (pure { r with ipaspace := PAS_Realm })
        | _ =>
          (do
            (Unreachable ())
            (pure r)) ) : SailM TLBIRecord )
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure ()))

def AArch64_TLBI_RPA (level : TLBILevel) (Xt : (BitVec 64)) (shareability : Shareability) : SailM Unit := do
  sail_assert (←((HaveRME ()) <&&> (do
    (pure ((← readReg PSTATE).EL == EL3))))) "src/v8_base.sail:36505.39-36505.40"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let range_bits ← (( do (undefined_int ()) ) : SailM Int )
  let p : Nat := 12
  let r : TLBIRecord := { r with op := TLBIOp_RPA }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := TLBI_AllAttr }
  let range_bits : Int :=
    match ((Sail.BitVec.extractLsb Xt 47 44) : BitVec 4) with
    | 0b0000 => 12
    | 0b0001 => 14
    | 0b0010 => 16
    | 0b0011 => 21
    | 0b0100 => 25
    | 0b0101 => 29
    | 0b0110 => 30
    | 0b0111 => 34
    | 0b1000 => 36
    | 0b1001 => 39
    | _ => 0
  let p ← (( do
    match (← (DecodePGS (_get_GPCCR_EL3_Type_PGS (← readReg GPCCR_EL3)))) with
    | .PGS_4KB => (pure 12)
    | .PGS_16KB => (pure 14)
    | .PGS_64KB => (pure 16) ) : SailM Int )
  let p := p
  let range_bits : Int :=
    if ((range_bits <b p) : Bool)
    then p
    else range_bits
  let range_bits := range_bits
  let BaseADDR : (BitVec 52) := (Zeros (n := 52))
  let BaseADDR ← (( do
    match ((_get_GPCCR_EL3_Type_PGS (← readReg GPCCR_EL3)) : BitVec 2) with
    | 0b00 => (pure (Sail.BitVec.updateSubrange BaseADDR 51 12 (Sail.BitVec.extractLsb Xt 39 0)))
    | 0b10 => (pure (Sail.BitVec.updateSubrange BaseADDR 51 14 (Sail.BitVec.extractLsb Xt 39 2)))
    | 0b01 => (pure (Sail.BitVec.updateSubrange BaseADDR 51 16 (Sail.BitVec.extractLsb Xt 39 4)))
    | _ => (pure BaseADDR) ) : SailM (BitVec 52) )
  sail_assert (range_bits ≥b 0) "src/v8_base.sail:36576.39-36576.40"
  sail_assert (52 ≥b range_bits) "src/v8_base.sail:36577.40-36577.41"
  let start_addr : (BitVec 52) := (BaseADDR &&& (Complement.complement (Sail.BitVec.zeroExtend (Ones (n := range_bits)) 52)))
  let end_addr_name : (BitVec 52) := (start_addr + (Sail.BitVec.zeroExtend (Ones (n := range_bits)) 52))
  let r : TLBIRecord := { r with address := (Sail.BitVec.zeroExtend start_addr 64) }
  let r : TLBIRecord := { r with end_address_name := (Sail.BitVec.zeroExtend end_addr_name 64) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_TLBI_PAALL (shareability : Shareability) : SailM Unit := do
  sail_assert (←((HaveRME ()) <&&> (do
    (pure ((← readReg PSTATE).EL == EL3))))) "src/v8_base.sail:36592.39-36592.40"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_PAALL }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := TLBI_AllAttr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch64_DC (regval : (BitVec 64)) (cachetype : CacheType) (cacheop : CacheOp) (opscope_in : CacheOpScope) : SailM Unit := do
  let ss ← (( do (undefined_SecurityState ()) ) : SailM SecurityState )
  let opscope : CacheOpScope := opscope_in
  let cache ← (( do (undefined_CacheRecord ()) ) : SailM CacheRecord )
  let cache : CacheRecord := { cache with acctype := AccessType_DC }
  let cache : CacheRecord := { cache with cachetype := cachetype }
  let cache : CacheRecord := { cache with cacheop := cacheop }
  let cache : CacheRecord := { cache with opscope := opscope }
  if ((BEq.beq opscope CacheOpScope_SetWay) : Bool)
  then
    (do
      let ss ← (( do (SecurityStateAtEL (← readReg PSTATE).EL) ) : SailM SecurityState )
      let cache : CacheRecord := { cache with cpas := (CPASAtSecurityState ss) }
      let cache : CacheRecord := { cache with shareability := Shareability_NSH }
      let cache ← (( do
        let (tup__0, tup__1, tup__2) ← do (DecodeSW regval cachetype)
        let cache : CacheRecord := { cache with setnum := tup__0 }
        let cache : CacheRecord := { cache with waynum := tup__1 }
        (pure { cache with level := tup__2 }) ) : SailM CacheRecord )
      let cache ← (( do
        if ((←((pure (BEq.beq cacheop CacheOp_Invalidate)) <&&> (do
             (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure ((_get_HCR_EL2_Type_SWIO (← readReg HCR_EL2)) == 1#1)) <||> (do
               (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) != 0b00#2)))))) : Bool)
        then (pure { cache with cacheop := CacheOp_CleanInvalidate })
        else (pure cache) ) : SailM CacheRecord )
      (CACHE_OP cache))
  else
    (do
      let cache ← (( do
        if ((←((EL2Enabled ()) <&&> (do
             (pure (! (← (IsInHost ()))))))) : Bool)
        then
          (do
            if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
                 (pure ((← readReg PSTATE).EL == EL1))))) : Bool)
            then
              (do
                let cache : CacheRecord := { cache with is_vmid_valid := true }
                (pure { cache with vmid := ← (do (VMID_read ())) }))
            else (pure { cache with is_vmid_valid := false }))
        else (pure { cache with is_vmid_valid := false }) ) : SailM CacheRecord )
      let cache ← (( do
        if (((← readReg PSTATE).EL == EL0) : Bool)
        then
          (do
            let cache : CacheRecord := { cache with is_asid_valid := true }
            (pure { cache with asid := ← (do (ASID_read ())) }))
        else (pure { cache with is_asid_valid := false }) ) : SailM CacheRecord )
      let opscope ← (( do
        if ((←((pure (BEq.beq opscope CacheOpScope_PoDP)) <&&> (do
             (__IMPDEF_boolean "Memory system does not supports PoDP")))) : Bool)
        then (pure CacheOpScope_PoP)
        else (pure opscope) ) : SailM CacheOpScope )
      let opscope ← (( do
        if ((←((pure (BEq.beq opscope CacheOpScope_PoP)) <&&> (do
             (__IMPDEF_boolean "Memory system does not supports PoP")))) : Bool)
        then (pure CacheOpScope_PoC)
        else (pure opscope) ) : SailM CacheOpScope )
      let vaddress : (BitVec 64) := regval
      let size : Int := 0
      let (size, vaddress) ← (( do
        if ((BEq.beq cacheop CacheOp_Invalidate) : Bool)
        then
          (do
            let size ← (__IMPDEF_integer "Data Cache Invalidate Watchpoint Size")
            sail_assert ((size ≥b (4 *i (2 ^i (BitVec.toNat (_get_CTR_EL0_Type_DminLine (← readReg CTR_EL0)))))) && (size ≤b 2048)) "src/v8_base.sail:36651.71-36651.72"
            sail_assert ((BitVec.toNat ((integer_subrange size 32 0) &&& (integer_subrange (size -i 1) 32 0))) == 0) "src/v8_base.sail:36652.61-36652.62"
            let vaddress : (BitVec 64) := (Align_bits regval size)
            (pure (size, vaddress)))
        else (pure (size, vaddress)) ) : SailM (Int × (BitVec 64)) )
      let size := size
      let cache ← (( do
        if ((← (DCInstNeedsTranslation opscope)) : Bool)
        then
          (do
            let cache : CacheRecord := { cache with vaddress := vaddress }
            let aligned : Bool := true
            let accdesc ← (( do (CreateAccDescDC cache) ) : SailM AccessDescriptor )
            let memaddrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) : SailM AddressDescriptor )
            if ((IsFault memaddrdesc) : Bool)
            then (AArch64_Abort regval memaddrdesc.fault)
            else (pure ())
            let cache : CacheRecord := { cache with translated := true }
            let cache : CacheRecord := { cache with paddress := memaddrdesc.paddress }
            let cache : CacheRecord := { cache with cpas := (CPASAtPAS memaddrdesc.paddress.paspace) }
            if (((BEq.beq opscope CacheOpScope_PoC) || ((BEq.beq opscope CacheOpScope_PoP) || (BEq.beq opscope CacheOpScope_PoDP))) : Bool)
            then (pure { cache with shareability := memaddrdesc.memattrs.shareability })
            else (pure { cache with shareability := Shareability_NSH }))
        else
          (do
            if ((BEq.beq opscope CacheOpScope_PoE) : Bool)
            then
              (do
                let cache : CacheRecord := { cache with translated := true }
                let cache : CacheRecord := { cache with shareability := Shareability_OSH }
                let cache : CacheRecord := { cache with paddress := { cache.paddress with address := (Sail.BitVec.extractLsb regval 55 0) } }
                let cache ← (pure { cache with paddress := ← (do (pure { cache.paddress with paspace := ← (do (DecodePASpace (BitVec.join1 [(BitVec.access regval 62)]) (BitVec.join1 [(BitVec.access regval 63)]))) })) })
                let cache : CacheRecord := { cache with cpas := (CPASAtPAS cache.paddress.paspace) }
                if ((bne cache.paddress.paspace PAS_Realm) : Bool)
                then (EndOfInstruction ())
                else (pure ())
                if ((← (__IMPDEF_boolean "Apply granule protection check on DC to PoE")) : Bool)
                then
                  (do
                    let memaddrdesc ← (( do (undefined_AddressDescriptor ()) ) : SailM AddressDescriptor )
                    let accdesc ← (( do (CreateAccDescDC cache) ) : SailM AccessDescriptor )
                    let memaddrdesc : AddressDescriptor := { memaddrdesc with paddress := cache.paddress }
                    let memaddrdesc ← (pure { memaddrdesc with fault := ← (do (pure { memaddrdesc.fault with gpcf := ← (do (GranuleProtectionCheck memaddrdesc accdesc)) })) })
                    if ((bne memaddrdesc.fault.gpcf.gpf GPCF_None) : Bool)
                    then
                      (do
                        let memaddrdesc : AddressDescriptor := { memaddrdesc with fault := { memaddrdesc.fault with statuscode := Fault_GPCFOnOutput } }
                        let memaddrdesc : AddressDescriptor := { memaddrdesc with fault := { memaddrdesc.fault with paddress := memaddrdesc.paddress } }
                        (AArch64_Abort (← (__UNKNOWN_bits 64)) memaddrdesc.fault))
                    else (pure ()))
                else (pure ())
                (pure cache))
            else
              (do
                if ((BEq.beq opscope CacheOpScope_PoPA) : Bool)
                then
                  (do
                    let cache : CacheRecord := { cache with translated := true }
                    let cache : CacheRecord := { cache with shareability := Shareability_OSH }
                    let cache : CacheRecord := { cache with paddress := { cache.paddress with address := (Sail.BitVec.extractLsb regval 55 0) } }
                    let cache ← (pure { cache with paddress := ← (do (pure { cache.paddress with paspace := ← (do (DecodePASpace (BitVec.join1 [(BitVec.access regval 62)]) (BitVec.join1 [(BitVec.access regval 63)]))) })) })
                    (pure { cache with cpas := (CPASAtPAS cache.paddress.paspace) }))
                else
                  (do
                    let cache : CacheRecord := { cache with vaddress := vaddress }
                    let cache : CacheRecord := { cache with translated := false }
                    let cache ← (pure { cache with shareability := ← (do (__UNKNOWN_Shareability ())) })
                    (pure { cache with paddress := ← (do (__UNKNOWN_FullAddress ())) })))) ) : SailM CacheRecord )
      let cache ← (( do
        if ((←((pure (BEq.beq cacheop CacheOp_Invalidate)) <&&> (do
             (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) != 0b00#2))))) : Bool)
        then (pure { cache with cacheop := CacheOp_CleanInvalidate })
        else (pure cache) ) : SailM CacheRecord )
      if ((←((pure (cache.translated && (BEq.beq cache.cpas CPAS_Secure))) <&&> (do
           (pure (! (← (HaveSecureState ()))))))) : Bool)
      then (pure ())
      else (do (CACHE_OP cache)))

def AArch64_MemZero (regval : (BitVec 64)) (cachetype : CacheType) : SailM Unit := do
  let size ← do (pure (4 *i (2 ^i (BitVec.toNat (_get_DCZID_EL0_Type_BS (← readReg DCZID_EL0))))))
  sail_assert (size ≤b MAX_ZERO_BLOCK_SIZE) "src/v8_base.sail:36724.38-36724.39"
  if ((← (HaveMTE2Ext ())) : Bool)
  then sail_assert (size ≥b TAG_GRANULE) "src/v8_base.sail:36726.34-36726.35"
  else (pure ())
  let vaddress : (BitVec 64) := (Align_bits regval size)
  let tagaccess : Bool := ((BEq.beq cachetype CacheType_Tag) || (BEq.beq cachetype CacheType_Data_Tag))
  let tagchecked : Bool := (BEq.beq cachetype CacheType_Data)
  let accdesc ← (( do (CreateAccDescDCZero tagaccess tagchecked) ) : SailM AccessDescriptor )
  if (((BEq.beq cachetype CacheType_Tag) || (BEq.beq cachetype CacheType_Data_Tag)) : Bool)
  then (AArch64_TagMemZero regval vaddress accdesc size)
  else (pure ())
  if (((BEq.beq cachetype CacheType_Data) || (BEq.beq cachetype CacheType_Data_Tag)) : Bool)
  then (AArch64_DataMemZero regval vaddress accdesc size)
  else (pure ())

def AArch64_IC__1 (regval : (BitVec 64)) (opscope : CacheOpScope) : SailM Unit := SailME.run do
  let ss ← (( do (undefined_SecurityState ()) ) : SailME Unit SecurityState )
  let cache ← (( do (undefined_CacheRecord ()) ) : SailME Unit CacheRecord )
  let cache : CacheRecord := { cache with acctype := AccessType_IC }
  let cache : CacheRecord := { cache with cachetype := CacheType_Instruction }
  let cache : CacheRecord := { cache with cacheop := CacheOp_Invalidate }
  let cache : CacheRecord := { cache with opscope := opscope }
  if (((BEq.beq opscope CacheOpScope_ALLU) || (BEq.beq opscope CacheOpScope_ALLUIS)) : Bool)
  then
    (do
      let ss ← (( do (SecurityStateAtEL (← readReg PSTATE).EL) ) : SailME Unit SecurityState )
      let cache : CacheRecord := { cache with cpas := (CPASAtSecurityState ss) }
      let cache ← (( do
        if ((←((pure (BEq.beq opscope CacheOpScope_ALLUIS)) <||> (do
             (pure (BEq.beq opscope CacheOpScope_ALLU)) <&&> (do
               (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure ((_get_HCR_EL2_Type_FB (← readReg HCR_EL2)) == 1#1)))))) : Bool)
        then (pure { cache with shareability := Shareability_ISH })
        else (pure { cache with shareability := Shareability_NSH }) ) : SailME Unit CacheRecord )
      let cache : CacheRecord := { cache with regval := regval }
      (CACHE_OP cache))
  else
    (do
      sail_assert (BEq.beq opscope CacheOpScope_PoU) "src/v8_base.sail:36768.42-36768.43"
      let cache ← (( do
        if ((←((EL2Enabled ()) <&&> (do
             (pure (! (← (IsInHost ()))))))) : Bool)
        then
          (do
            if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
                 (pure ((← readReg PSTATE).EL == EL1))))) : Bool)
            then
              (do
                let cache : CacheRecord := { cache with is_vmid_valid := true }
                (pure { cache with vmid := ← (do (VMID_read ())) }))
            else (pure { cache with is_vmid_valid := false }))
        else (pure { cache with is_vmid_valid := false }) ) : SailME Unit CacheRecord )
      let cache ← (( do
        if (((← readReg PSTATE).EL == EL0) : Bool)
        then
          (do
            let cache : CacheRecord := { cache with is_asid_valid := true }
            (pure { cache with asid := ← (do (ASID_read ())) }))
        else (pure { cache with is_asid_valid := false }) ) : SailME Unit CacheRecord )
      let vaddress : (BitVec 64) := regval
      let need_translate ← (( do (ICInstNeedsTranslation opscope) ) : SailME Unit Bool )
      let cache : CacheRecord := { cache with vaddress := regval }
      let cache : CacheRecord := { cache with shareability := Shareability_NSH }
      let cache : CacheRecord := { cache with translated := need_translate }
      if ((! need_translate) : Bool)
      then
        (do
          let cache ← (( do (pure { cache with paddress := ← (do (__UNKNOWN_FullAddress ())) }) ) : SailME Unit CacheRecord )
          (CACHE_OP cache)
          SailME.throw ())
      else
        (do
          let accdesc ← (( do (CreateAccDescIC cache) ) : SailME Unit AccessDescriptor )
          let aligned : Bool := true
          let size := 0
          let memaddrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) : SailME Unit AddressDescriptor )
          if ((IsFault memaddrdesc) : Bool)
          then (AArch64_Abort regval memaddrdesc.fault)
          else (pure ())
          let cache : CacheRecord := { cache with cpas := (CPASAtPAS memaddrdesc.paddress.paspace) }
          let cache : CacheRecord := { cache with paddress := memaddrdesc.paddress }
          (CACHE_OP cache)))

def AArch64_RestrictPrediction (val_name : (BitVec 64)) (restriction : RestrictType) : SailM Unit := do
  let c ← (( do (undefined_ExecutionCntxt ()) ) : SailM ExecutionCntxt )
  let target_el : (BitVec 2) := (Sail.BitVec.extractLsb val_name 25 24)
  if ((←((pure (! (HaveEL target_el))) <||> (do
       (pure ((BitVec.toNat target_el) >b (BitVec.toNat (← readReg PSTATE).EL)))))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  let ns : (BitVec 1) := (BitVec.join1 [(BitVec.access val_name 26)])
  let nse : (BitVec 1) := (BitVec.join1 [(BitVec.access val_name 27)])
  let ss ← (( do (TargetSecurityState ns nse) ) : SailM SecurityState )
  if (((BEq.beq ss SS_Root) && (target_el != EL3)) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  if ((((! (← (HaveRME ()))) && (target_el == EL3)) && (bne ss SS_Secure)) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  let c : ExecutionCntxt := { c with security := ss }
  let c : ExecutionCntxt := { c with target_el := target_el }
  let c ← (( do
    if ((← (EL2Enabled ())) : Bool)
    then
      (do
        if ((←((pure ((← readReg PSTATE).EL == EL0)) <&&> (do
             (pure (! (← (IsInHost ()))))) <||> (do
             (pure ((← readReg PSTATE).EL == EL1))))) : Bool)
        then
          (do
            let c : ExecutionCntxt := { c with is_vmid_valid := true }
            let c : ExecutionCntxt := { c with all_vmid := false }
            (pure { c with vmid := ← (do (VMID_read ())) }))
        else
          (do
            if (((←((pure (target_el == EL0)) <&&> (do
                   (pure (! (← (ELIsInHost target_el))))))) || (target_el == EL1)) : Bool)
            then
              (let c : ExecutionCntxt := { c with is_vmid_valid := true }
              let c : ExecutionCntxt := { c with all_vmid := ((BitVec.join1 [(BitVec.access val_name 48)]) == 1#1) }
              (pure { c with vmid := (Sail.BitVec.extractLsb val_name 47 32) }))
            else (pure { c with is_vmid_valid := false })))
    else (pure { c with is_vmid_valid := false }) ) : SailM ExecutionCntxt )
  let c ← (( do
    if (((← readReg PSTATE).EL == EL0) : Bool)
    then
      (do
        let c : ExecutionCntxt := { c with is_asid_valid := true }
        let c : ExecutionCntxt := { c with all_asid := false }
        (pure { c with asid := ← (do (ASID_read ())) }))
    else
      (if ((target_el == EL0) : Bool)
      then
        (let c : ExecutionCntxt := { c with is_asid_valid := true }
        let c : ExecutionCntxt := { c with all_asid := ((BitVec.join1 [(BitVec.access val_name 16)]) == 1#1) }
        (pure { c with asid := (Sail.BitVec.extractLsb val_name 15 0) }))
      else (pure { c with is_asid_valid := false })) ) : SailM ExecutionCntxt )
  let c : ExecutionCntxt := { c with restriction := restriction }
  (pure (RESTRICT_PREDICTIONS c))

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV83 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap3_IMPLEMENTED enabled
  if (enabled : Bool)
  then (__ConfigureV82 enabled)
  else (pure ())

def AArch32_DC (regval : (BitVec 32)) (cacheop : CacheOp) (opscope : CacheOpScope) : SailM Unit := do
  let cache ← (( do (undefined_CacheRecord ()) ) : SailM CacheRecord )
  let cache : CacheRecord := { cache with acctype := AccessType_DC }
  let cache : CacheRecord := { cache with cacheop := cacheop }
  let cache : CacheRecord := { cache with opscope := opscope }
  let cache : CacheRecord := { cache with cachetype := CacheType_Data }
  let cache ← (pure { cache with security := ← (do (SecurityStateAtEL (← readReg PSTATE).EL)) })
  if ((BEq.beq opscope CacheOpScope_SetWay) : Bool)
  then
    (do
      let cache : CacheRecord := { cache with shareability := Shareability_NSH }
      let cache ← (( do
        let (tup__0, tup__1, tup__2) ← do (DecodeSW (Sail.BitVec.zeroExtend regval 64) CacheType_Data)
        let cache : CacheRecord := { cache with setnum := tup__0 }
        let cache : CacheRecord := { cache with waynum := tup__1 }
        (pure { cache with level := tup__2 }) ) : SailM CacheRecord )
      let cache ← (( do
        if ((←((pure (BEq.beq cacheop CacheOp_Invalidate)) <&&> (do
             (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2)))) <&&> (do
               (pure ((_get_HCR_EL2_Type_SWIO (← readReg HCR_EL2)) == 1#1)) <||> (do
                 (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) != 0b00#2)))) <||> (do
               (ELUsingAArch32 EL2) <&&> (do
                 (pure ((_get_HCR_Type_SWIO (← (HCR_read ()))) == 1#1)) <||> (do
                   (pure (((_get_HCR_Type_DC (← (HCR_read ()))) +++ (_get_HCR_Type_VM (← (HCR_read ())))) != 0b00#2)))))))) : Bool)
        then (pure { cache with cacheop := CacheOp_CleanInvalidate })
        else (pure cache) ) : SailM CacheRecord )
      (CACHE_OP cache))
  else
    (do
      let cache ← (( do
        if ((← (EL2Enabled ())) : Bool)
        then
          (do
            if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
                 (pure ((← readReg PSTATE).EL == EL1))))) : Bool)
            then
              (do
                let cache : CacheRecord := { cache with is_vmid_valid := true }
                (pure { cache with vmid := ← (do (VMID_read ())) }))
            else (pure { cache with is_vmid_valid := false }))
        else (pure { cache with is_vmid_valid := false }) ) : SailM CacheRecord )
      let cache ← (( do
        if (((← readReg PSTATE).EL == EL0) : Bool)
        then
          (do
            let cache : CacheRecord := { cache with is_asid_valid := true }
            (pure { cache with asid := ← (do (ASID_read ())) }))
        else (pure { cache with is_asid_valid := false }) ) : SailM CacheRecord )
      let need_translate ← (( do (DCInstNeedsTranslation opscope) ) : SailM Bool )
      let vaddress : (BitVec 32) := regval
      let size : Int := 0
      let (size, vaddress) ← (( do
        if ((BEq.beq cacheop CacheOp_Invalidate) : Bool)
        then
          (do
            let size ← (__IMPDEF_integer "Data Cache Invalidate Watchpoint Size")
            sail_assert ((size ≥b (4 *i (2 ^i (BitVec.toNat (_get_CTR_EL0_Type_DminLine (← readReg CTR_EL0)))))) && (size ≤b 2048)) "src/v8_base.sail:40907.71-40907.72"
            sail_assert ((BitVec.toNat ((integer_subrange size 32 0) &&& (integer_subrange (size -i 1) 32 0))) == 0) "src/v8_base.sail:40908.61-40908.62"
            let vaddress : (BitVec 32) := (Align_bits regval size)
            (pure (size, vaddress)))
        else (pure (size, vaddress)) ) : SailM (Int × (BitVec 32)) )
      let size := size
      let cache : CacheRecord := { cache with translated := need_translate }
      let cache : CacheRecord := { cache with vaddress := (Sail.BitVec.zeroExtend vaddress 64) }
      let cache ← (( do
        if (need_translate : Bool)
        then
          (do
            let aligned : Bool := true
            let accdesc ← (( do (CreateAccDescDC cache) ) : SailM AccessDescriptor )
            let memaddrdesc ← (( do (AArch32_TranslateAddress vaddress accdesc aligned size) ) : SailM AddressDescriptor )
            if ((IsFault memaddrdesc) : Bool)
            then (AArch32_Abort regval memaddrdesc.fault)
            else (pure ())
            let cache : CacheRecord := { cache with paddress := memaddrdesc.paddress }
            if ((BEq.beq opscope CacheOpScope_PoC) : Bool)
            then (pure { cache with shareability := memaddrdesc.memattrs.shareability })
            else (pure { cache with shareability := Shareability_NSH }))
        else
          (do
            let cache ← (pure { cache with shareability := ← (do (__UNKNOWN_Shareability ())) })
            (pure { cache with paddress := ← (do (__UNKNOWN_FullAddress ())) })) ) : SailM CacheRecord )
      let cache ← (( do
        if ((←((pure (BEq.beq cacheop CacheOp_Invalidate)) <&&> (do
             (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure (! (← (ELUsingAArch32 EL2)))) <&&> (do
               (pure (((_get_HCR_EL2_Type_DC (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VM (← readReg HCR_EL2))) != 0b00#2))) <||> (do
               (ELUsingAArch32 EL2) <&&> (do
                 (pure (((_get_HCR_Type_DC (← (HCR_read ()))) +++ (_get_HCR_Type_VM (← (HCR_read ())))) != 0b00#2))))))) : Bool)
        then (pure { cache with cacheop := CacheOp_CleanInvalidate })
        else (pure cache) ) : SailM CacheRecord )
      (CACHE_OP cache))

def AArch32_IC__1 (regval : (BitVec 32)) (opscope : CacheOpScope) : SailM Unit := SailME.run do
  let need_translate ← (( do (undefined_bool ()) ) : SailME Unit Bool )
  let cache ← (( do (undefined_CacheRecord ()) ) : SailME Unit CacheRecord )
  let cache : CacheRecord := { cache with acctype := AccessType_IC }
  let cache : CacheRecord := { cache with cachetype := CacheType_Instruction }
  let cache : CacheRecord := { cache with cacheop := CacheOp_Invalidate }
  let cache : CacheRecord := { cache with opscope := opscope }
  let cache ← (pure { cache with security := ← (do (SecurityStateAtEL (← readReg PSTATE).EL)) })
  if (((BEq.beq opscope CacheOpScope_ALLU) || (BEq.beq opscope CacheOpScope_ALLUIS)) : Bool)
  then
    (do
      let cache ← (( do
        if ((←((pure (BEq.beq opscope CacheOpScope_ALLUIS)) <||> (do
             (pure (BEq.beq opscope CacheOpScope_ALLU)) <&&> (do
               (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
               (EL2Enabled ())) <&&> (do
               (pure ((_get_HCR_Type_FB (← (HCR_read ()))) == 1#1)))))) : Bool)
        then (pure { cache with shareability := Shareability_ISH })
        else (pure { cache with shareability := Shareability_NSH }) ) : SailME Unit CacheRecord )
      let cache : CacheRecord := { cache with regval := (Sail.BitVec.zeroExtend regval 64) }
      (CACHE_OP cache))
  else
    (do
      sail_assert (BEq.beq opscope CacheOpScope_PoU) "src/v8_base.sail:40964.42-40964.43"
      let cache ← (( do
        if ((← (EL2Enabled ())) : Bool)
        then
          (do
            if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
                 (pure ((← readReg PSTATE).EL == EL1))))) : Bool)
            then
              (do
                let cache : CacheRecord := { cache with is_vmid_valid := true }
                (pure { cache with vmid := ← (do (VMID_read ())) }))
            else (pure { cache with is_vmid_valid := false }))
        else (pure { cache with is_vmid_valid := false }) ) : SailME Unit CacheRecord )
      let cache ← (( do
        if (((← readReg PSTATE).EL == EL0) : Bool)
        then
          (do
            let cache : CacheRecord := { cache with is_asid_valid := true }
            (pure { cache with asid := ← (do (ASID_read ())) }))
        else (pure { cache with is_asid_valid := false }) ) : SailME Unit CacheRecord )
      let need_translate ← (( do (ICInstNeedsTranslation opscope) ) : SailME Unit Bool )
      let cache : CacheRecord := { cache with shareability := Shareability_NSH }
      let cache : CacheRecord := { cache with vaddress := (Sail.BitVec.zeroExtend regval 64) }
      let cache : CacheRecord := { cache with translated := need_translate }
      if ((! need_translate) : Bool)
      then
        (do
          let cache ← (( do (pure { cache with paddress := ← (do (__UNKNOWN_FullAddress ())) }) ) : SailME Unit CacheRecord )
          (CACHE_OP cache)
          SailME.throw ())
      else
        (do
          let size := 0
          let aligned : Bool := true
          let accdesc ← (( do (CreateAccDescIC cache) ) : SailME Unit AccessDescriptor )
          let memaddrdesc ← (( do (AArch32_TranslateAddress regval accdesc aligned size) ) : SailME Unit AddressDescriptor )
          if ((IsFault memaddrdesc) : Bool)
          then (AArch32_Abort regval memaddrdesc.fault)
          else (pure ())
          let cache : CacheRecord := { cache with paddress := memaddrdesc.paddress }
          (CACHE_OP cache)))

def AArch32_EncodePARLD (addrdesc : AddressDescriptor) (ss : SecurityState) : SailM Unit := do
  if ((! (IsFault addrdesc)) : Bool)
  then
    (do
      let ns ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let ns ← (( do
        if ((BEq.beq ss SS_NonSecure) : Bool)
        then (do (__UNKNOWN_bit ()))
        else
          (if ((BEq.beq addrdesc.paddress.paspace PAS_Secure) : Bool)
          then (pure 0#1)
          else (pure 1#1)) ) : SailM (BitVec 1) )
      let ns : (BitVec 1) :=
        if ((BEq.beq addrdesc.paddress.paspace PAS_Secure) : Bool)
        then 0#1
        else 1#1
      (PAR_write (_update_PAR_Type_F (← (PAR_read ())) 0#1))
      (PAR_write (_update_PAR_Type_SH (← (PAR_read ())) (← (ReportedPARShareability (PAREncodeShareability addrdesc.memattrs)))))
      (PAR_write (_update_PAR_Type_NS (← (PAR_read ())) ns))
      (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange (← (PAR_read ())) 10 10 (← (__IMPDEF_bit "Non-Faulting PAR")))))
      (PAR_write (_update_PAR_Type_LPAE (← (PAR_read ())) 1#1))
      (PAR_write (_update_PAR_Type_PA (← (PAR_read ())) (Sail.BitVec.extractLsb addrdesc.paddress.address 39 12)))
      (PAR_write (_update_PAR_Type_ATTR (← (PAR_read ())) (← (ReportedPARAttrs (← (EncodePARAttrs addrdesc.memattrs)))))))
  else
    (do
      (PAR_write (_update_PAR_Type_F (← (PAR_read ())) 1#1))
      (PAR_write (_update_PAR_Type_FST (← (PAR_read ())) (← (AArch32_PARFaultStatusLD addrdesc.fault))))
      (PAR_write
        (_update_PAR_Type_S2WLK (← (PAR_read ()))
          (if (addrdesc.fault.s2fs1walk : Bool)
          then 1#1
          else 0#1)))
      (PAR_write
        (_update_PAR_Type_FSTAGE (← (PAR_read ()))
          (if (addrdesc.fault.secondstage : Bool)
          then 1#1
          else 0#1)))
      (PAR_write (_update_PAR_Type_LPAE (← (PAR_read ())) 1#1))
      (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange (← (PAR_read ())) 63 48 (← (__IMPDEF_bits 16 "Faulting PAR"))))))

def AArch32_EncodePARSD (addrdesc_in : AddressDescriptor) (supersection : (BitVec 1)) (ss : SecurityState) : SailM Unit := do
  let addrdesc : AddressDescriptor := addrdesc_in
  if ((! (IsFault addrdesc)) : Bool)
  then
    (do
      let addrdesc : AddressDescriptor :=
        if (((BEq.beq addrdesc.memattrs.memtype MemType_Device) || ((addrdesc.memattrs.inner.attrs == MemAttr_NC) && (addrdesc.memattrs.outer.attrs == MemAttr_NC))) : Bool)
        then { addrdesc with memattrs := { addrdesc.memattrs with shareability := Shareability_OSH } }
        else addrdesc
      let ns ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let ns ← (( do
        if ((BEq.beq ss SS_NonSecure) : Bool)
        then (do (__UNKNOWN_bit ()))
        else
          (if ((BEq.beq addrdesc.paddress.paspace PAS_Secure) : Bool)
          then (pure 0#1)
          else (pure 1#1)) ) : SailM (BitVec 1) )
      let ns : (BitVec 1) :=
        if ((BEq.beq addrdesc.paddress.paspace PAS_Secure) : Bool)
        then 0#1
        else 1#1
      let sh : (BitVec 2) :=
        if ((bne addrdesc.memattrs.shareability Shareability_NSH) : Bool)
        then 0b01#2
        else 0b00#2
      (PAR_write (_update_PAR_Type_F (← (PAR_read ())) 0#1))
      (PAR_write (_update_PAR_Type_SS (← (PAR_read ())) supersection))
      (PAR_write (_update_PAR_Type_Outer (← (PAR_read ())) (← (AArch32_ReportedOuterAttrs (← (AArch32_PAROuterAttrs addrdesc.memattrs))))))
      (PAR_write (_update_PAR_Type_Inner (← (PAR_read ())) (← (AArch32_ReportedInnerAttrs (← (AArch32_PARInnerAttrs addrdesc.memattrs))))))
      (PAR_write (_update_PAR_Type_SH (← (PAR_read ())) (← (ReportedPARShareability sh))))
      (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange (← (PAR_read ())) 8 8 (← (__IMPDEF_bit "Non-Faulting PAR")))))
      (PAR_write (_update_PAR_Type_NS (← (PAR_read ())) ns))
      (PAR_write
        (_update_PAR_Type_NOS (← (PAR_read ()))
          (if ((BEq.beq addrdesc.memattrs.shareability Shareability_OSH) : Bool)
          then 0#1
          else 1#1)))
      (PAR_write (_update_PAR_Type_LPAE (← (PAR_read ())) 0#1))
      (PAR_write (_update_PAR_Type_PA (← (PAR_read ())) (Sail.BitVec.extractLsb addrdesc.paddress.address 39 12))))
  else
    (do
      (PAR_write (_update_PAR_Type_F (← (PAR_read ())) 1#1))
      (PAR_write (_update_PAR_Type_FST (← (PAR_read ())) (← (AArch32_PARFaultStatusSD addrdesc.fault))))
      (PAR_write (_update_PAR_Type_LPAE (← (PAR_read ())) 0#1))
      (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange (← (PAR_read ())) 31 16 (← (__IMPDEF_bits 16 "Faulting PAR"))))))

def AArch32_RestrictPrediction (val_name : (BitVec 32)) (restriction : RestrictType) : SailM Unit := do
  let c ← (( do (undefined_ExecutionCntxt ()) ) : SailM ExecutionCntxt )
  let target_el : (BitVec 2) := (Sail.BitVec.extractLsb val_name 25 24)
  if ((←((pure (! (HaveEL target_el))) <||> (do
       (pure ((BitVec.toNat target_el) >b (BitVec.toNat (← readReg PSTATE).EL)))))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  let ns : (BitVec 1) := (BitVec.join1 [(BitVec.access val_name 26)])
  let nse ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
  let ss ← (( do (TargetSecurityState ns nse) ) : SailM SecurityState )
  let c : ExecutionCntxt := { c with security := ss }
  let c : ExecutionCntxt := { c with target_el := target_el }
  let c ← (( do
    if ((← (EL2Enabled ())) : Bool)
    then
      (do
        if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
             (pure ((← readReg PSTATE).EL == EL1))))) : Bool)
        then
          (do
            let c : ExecutionCntxt := { c with is_vmid_valid := true }
            let c : ExecutionCntxt := { c with all_vmid := false }
            (pure { c with vmid := ← (do (VMID_read ())) }))
        else
          (if (((target_el == EL0) || (target_el == EL1)) : Bool)
          then
            (let c : ExecutionCntxt := { c with is_vmid_valid := true }
            let c : ExecutionCntxt := { c with all_vmid := ((BitVec.join1 [(BitVec.access val_name 27)]) == 1#1) }
            (pure { c with vmid := (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb val_name 23 16) 16) }))
          else (pure { c with is_vmid_valid := false })))
    else (pure { c with is_vmid_valid := false }) ) : SailM ExecutionCntxt )
  let c ← (( do
    if (((← readReg PSTATE).EL == EL0) : Bool)
    then
      (do
        let c : ExecutionCntxt := { c with is_asid_valid := true }
        let c : ExecutionCntxt := { c with all_asid := false }
        (pure { c with asid := ← (do (ASID_read ())) }))
    else
      (if ((target_el == EL0) : Bool)
      then
        (let c : ExecutionCntxt := { c with is_asid_valid := true }
        let c : ExecutionCntxt := { c with all_asid := ((BitVec.join1 [(BitVec.access val_name 8)]) == 1#1) }
        (pure { c with asid := (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb val_name 7 0) 16) }))
      else (pure { c with is_asid_valid := false })) ) : SailM ExecutionCntxt )
  let c : ExecutionCntxt := { c with restriction := restriction }
  (pure (RESTRICT_PREDICTIONS c))

def A32ExpandImm_C (imm12 : (BitVec 12)) (carry_in : (BitVec 1)) : SailM ((BitVec 32) × (BitVec 1)) := do
  let carry_out ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let unrotated_value : (BitVec 32) := (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb imm12 7 0) 32)
  let (carry_out, imm32) ← (( do
    let (tup__0, tup__1) ← do (Shift_C unrotated_value SRType_ROR (2 *i (BitVec.toNat (Sail.BitVec.extractLsb imm12 11 8))) carry_in)
    let imm32 : (BitVec 32) := tup__0
    let carry_out : (BitVec 1) := tup__1
    (pure (carry_out, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (pure (imm32, carry_out))

/-- Type quantifiers: k_N : Nat, amount : Int, k_N ≥ 0 -/
def Shift (value_name : (BitVec k_N)) (srtype : SRType) (amount : Int) (carry_in : (BitVec 1)) : SailM (BitVec k_N) := do
  let result ← (( do (undefined_bitvector (Sail.BitVec.length value_name)) ) : SailM (BitVec k_N) )
  let (__tup_0, _) ← do (Shift_C value_name srtype amount carry_in)
  (pure __tup_0)

/-- Type quantifiers: ec : Int -/
def AArch32_SystemAccessTrapSyndrome (instr : (BitVec 32)) (ec : Int) : SailM ExceptionRecord := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  let except ← (( do
    match ec with
    | 0 => (do (ExceptionSyndrome Exception_Uncategorized))
    | 3 => (do (ExceptionSyndrome Exception_CP15RTTrap))
    | 4 => (do (ExceptionSyndrome Exception_CP15RRTTrap))
    | 5 => (do (ExceptionSyndrome Exception_CP14RTTrap))
    | 6 => (do (ExceptionSyndrome Exception_CP14DTTrap))
    | 7 => (do (ExceptionSyndrome Exception_AdvSIMDFPAccessTrap))
    | 8 => (do (ExceptionSyndrome Exception_FPIDTrap))
    | 12 => (do (ExceptionSyndrome Exception_CP14RRTTrap))
    | _ =>
      (do
        (Unreachable ())
        (pure except)) ) : SailM ExceptionRecord )
  let iss : (BitVec 20) := (Zeros (n := 20))
  if ((BEq.beq except.exceptype Exception_Uncategorized) : Bool)
  then (pure except)
  else
    (do
      let iss ← (( do
        if (((BEq.beq except.exceptype Exception_FPIDTrap) || ((BEq.beq except.exceptype Exception_CP14RTTrap) || (BEq.beq except.exceptype Exception_CP15RTTrap))) : Bool)
        then
          (let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 13 10 (Sail.BitVec.extractLsb instr 19 16))
          let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 8 5 (Sail.BitVec.extractLsb instr 15 12))
          let iss : (BitVec 20) := (BitVec.update iss 9 (Bit 0#1))
          if ((bne except.exceptype Exception_FPIDTrap) : Bool)
          then
            (let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 19 17 (Sail.BitVec.extractLsb instr 7 5))
            let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 16 14 (Sail.BitVec.extractLsb instr 23 21))
            (pure (Sail.BitVec.updateSubrange iss 4 1 (Sail.BitVec.extractLsb instr 3 0))))
          else
            (let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 19 17 0b000#3)
            let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 16 14 0b111#3)
            (pure (Sail.BitVec.updateSubrange iss 4 1 0b0000#4))))
        else
          (do
            if (((BEq.beq except.exceptype Exception_CP14RRTTrap) || ((BEq.beq except.exceptype Exception_AdvSIMDFPAccessTrap) || (BEq.beq except.exceptype Exception_CP15RRTTrap))) : Bool)
            then
              (let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 19 16 (Sail.BitVec.extractLsb instr 7 4))
              let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 13 10 (Sail.BitVec.extractLsb instr 19 16))
              let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 8 5 (Sail.BitVec.extractLsb instr 15 12))
              (pure (Sail.BitVec.updateSubrange iss 4 1 (Sail.BitVec.extractLsb instr 3 0))))
            else
              (do
                if ((BEq.beq except.exceptype Exception_CP14DTTrap) : Bool)
                then
                  (do
                    let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 19 12 (Sail.BitVec.extractLsb instr 7 0))
                    let iss : (BitVec 20) := (BitVec.update iss 4 (Bit (BitVec.join1 [(BitVec.access instr 23)])))
                    let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 2 1 ((BitVec.join1 [(BitVec.access instr 24)]) +++ (BitVec.join1 [(BitVec.access instr 21)])))
                    if (((Sail.BitVec.extractLsb instr 19 16) == 0b1111#4) : Bool)
                    then
                      (do
                        let iss ← (pure (Sail.BitVec.updateSubrange iss 8 5 (← (__UNKNOWN_bits 4))))
                        (pure (BitVec.update iss 3 (Bit 1#1))))
                    else (pure iss))
                else (pure iss))) ) : SailM (BitVec 20) )
      let iss : (BitVec 20) := (BitVec.update iss 0 (Bit (BitVec.join1 [(BitVec.access instr 20)])))
      let except ← (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 24 20 (← (ConditionSyndrome ()))))) })
      (pure { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 0 iss) }))

/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def Mem_with_type_read (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) : SailM (BitVec (size * 8)) := do
  let ispair : Bool := false
  (Mem_with_type_read__1 address size accdesc ispair)

/-- Type quantifiers: k_ispair : Bool, size : Nat, (size * 8) ≥ 0 -/
def Mem_with_type_set__1 (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) (ispair : Bool) (value_in_name : (BitVec (size * 8))) : SailM Unit := do
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let halfsize := (Int.ediv size 2)
  let value_name : (BitVec (size * 8)) := value_in_name
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
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then
      (do
        sail_assert (((size *i 8) == 8) || (((size *i 8) == 16) || (((size *i 8) == 32) || (((size *i 8) == 64) || ((size *i 8) == 128))))) "src/v8_base.sail:42031.116-42031.117"
        (pure (reverse_endianness value_name)))
    else (pure value_name) ) : SailM (BitVec (size * 8)) )
  if (aligned : Bool)
  then
    (do
      sail_assert (((((size == 1) || (size == 2)) || (size == 4)) || (size == 8)) || (size == 16)) "src/v8_base.sail:42035.52-42035.53"
      (AArch32_MemSingle_set__1 address size accdesc aligned ispair value_name))
  else
    (do
      sail_assert (size >b 1) "src/v8_base.sail:42038.23-42038.24"
      (AArch32_MemSingle_set address 1 accdesc aligned (Sail.BitVec.extractLsb value_name 7 0))
      let c ← (( do (ConstrainUnpredictable Unpredictable_DEVPAGE2) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_FAULT) || (BEq.beq c Constraint_NONE)) "src/v8_base.sail:42041.59-42041.60"
      let aligned : Bool :=
        if ((BEq.beq c Constraint_NONE) : Bool)
        then true
        else aligned
      let loop_i_lower := 1
      let loop_i_upper := (size -i 1)
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do (AArch32_MemSingle_set (BitVec.addInt address i) 1 accdesc aligned (Sail.BitVec.extractLsb value_name ((8 *i i) +i 7) (8 *i i)))
      (pure loop_vars))

def ALUWritePC (address : (BitVec 32)) : SailM Unit := do
  if ((BEq.beq (← (CurrentInstrSet ())) InstrSet_A32) : Bool)
  then (BXWritePC address BranchType_INDIR)
  else (BranchWritePC address BranchType_INDIR)

def LoadWritePC (address : (BitVec 32)) : SailM Unit := do
  (BXWritePC address BranchType_INDIR)

/-- Type quantifiers: N : Nat, i : Int, k_is_unsigned : Bool, N ≥ 0 -/
def Sat (i : Int) (N : Nat) (is_unsigned : Bool) : SailM (BitVec N) := do
  if (is_unsigned : Bool)
  then
    (do
      sail_assert (0 ≤b (N -i 1)) "src/v8_base.sail:42744.38-42744.39"
      (UnsignedSat i N))
  else
    (do
      sail_assert (0 ≤b (N -i 1)) "src/v8_base.sail:42747.38-42747.39"
      (SignedSat i N))

def AArch32_vESBOperation (_ : Unit) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
    (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
    (EL2Enabled ())))) "src/v8_base.sail:42806.63-42806.64"
  if ((! (← (ELUsingAArch32 EL2))) : Bool)
  then (do (AArch64_vESBOperation ()))
  else
    (do
      let vSEI_enabled ← (( do (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 0#1)) <&&> (do (pure ((_get_HCR_Type_AMO (← (HCR_read ()))) == 1#1))) ) : SailM Bool )
      let vSEI_pending ← (( do (pure vSEI_enabled) <&&> (do (pure ((_get_HCR_Type_VA (← (HCR_read ()))) == 1#1))) ) : SailM Bool )
      let vintdis ← (( do (Halted ()) <||> (do (ExternalDebugInterruptsDisabled EL1)) ) : SailM Bool )
      let vmasked ← (( do (pure vintdis) <||> (do (pure ((← readReg PSTATE).A == 1#1))) ) : SailM Bool )
      if ((vSEI_pending && vmasked) : Bool)
      then
        (do
          let syndrome : (BitVec 32) := (Zeros (n := 32))
          let syndrome : (BitVec 32) := (BitVec.update syndrome 31 (Bit 1#1))
          let syndrome ← (pure (Sail.BitVec.updateSubrange syndrome 15 14 (Sail.BitVec.extractLsb (← (VDFSR_read ())) 15 14)))
          let syndrome ← (pure (BitVec.update syndrome 12 (Bit (BitVec.join1 [(BitVec.access (← (VDFSR_read ())) 12)]))))
          let syndrome ← (pure (BitVec.update syndrome 9 (Bit (_get_TTBCR_Type_EAE (← (TTBCR_read ()))))))
          let syndrome ← (( do
            if (((_get_TTBCR_Type_EAE (← (TTBCR_read ()))) == 1#1) : Bool)
            then (pure (Sail.BitVec.updateSubrange syndrome 5 0 0b010001#6))
            else
              (let syndrome : (BitVec 32) := (Sail.BitVec.updateSubrange syndrome 10 10 (Sail.BitVec.extractLsb 0b10110#5 4 4))
              (pure (Sail.BitVec.updateSubrange syndrome 3 0 (Sail.BitVec.extractLsb 0b10110#5 3 0)))) ) : SailM (BitVec 32) )
          (VDISR_write (Mk_VDISR_Type syndrome))
          (HCR_write (_update_HCR_Type_VA (← (HCR_read ())) 0#1)))
      else (pure ()))

def AArch32_CallHypervisor (immediate : (BitVec 16)) : SailM Unit := do
  sail_assert (HaveEL EL2) "src/v8_base.sail:42929.22-42929.23"
  if ((! (← (ELUsingAArch32 EL2))) : Bool)
  then (AArch64_CallHypervisor immediate)
  else (AArch32_TakeHVCException immediate)

def AArch32_CallSupervisor (immediate_in : (BitVec 16)) : SailM Unit := do
  let immediate : (BitVec 16) := immediate_in
  let immediate ← (( do
    if (((← (AArch32_CurrentCond ())) != 0b1110#4) : Bool)
    then (do (__UNKNOWN_bits 16))
    else (pure immediate) ) : SailM (BitVec 16) )
  if ((← (AArch32_GeneralExceptionsToAArch64 ())) : Bool)
  then (AArch64_CallSupervisor immediate)
  else (AArch32_TakeSVCException immediate)

def AArch32_ClearEventCounters (_ : Unit) : SailM Unit := do
  if ((← (HaveAArch64 ())) : Bool)
  then (do (AArch64_ClearEventCounters ()))
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
              sail_assert (0 ≤b idx) "src/v8_base.sail:43512.45-43512.46"
              sail_assert (idx <b 31) "src/v8_base.sail:43513.45-43513.46"
              (PMEVCNTR_set idx (Zeros (n := 32)))
          (pure loop_vars))
      else (pure ()))

def AArch32_DTLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:43614.65-43614.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_DALL }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_DTLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:43632.65-43632.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_DASID }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_DTLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:43652.65-43652.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_DVA }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  let r : TLBIRecord := { r with address := (((Zeros (n := 32)) +++ (Sail.BitVec.extractLsb Rt 31 12)) +++ (Zeros (n := 12))) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_ITLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:43673.65-43673.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IALL }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_ITLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:43691.65-43691.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IASID }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_ITLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:43711.65-43711.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IVA }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  let r : TLBIRecord := { r with address := (((Zeros (n := 32)) +++ (Sail.BitVec.extractLsb Rt 31 12)) +++ (Zeros (n := 12))) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_TLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2))))) "src/v8_base.sail:43732.46-43732.47"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ALL }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_TLBI_VMALL (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:43750.65-43750.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VMALL }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_TLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:43769.65-43769.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ASID }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_TLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:43789.65-43789.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VA }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  let r : TLBIRecord := { r with address := (((Zeros (n := 32)) +++ (Sail.BitVec.extractLsb Rt 31 12)) +++ (Zeros (n := 12))) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_TLBI_VAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2)) <||> (do
      (pure ((← readReg PSTATE).EL == EL1)))))) "src/v8_base.sail:43810.65-43810.66"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VAA }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with address := (((Zeros (n := 32)) +++ (Sail.BitVec.extractLsb Rt 31 12)) +++ (Zeros (n := 12))) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def AArch32_TLBI_IPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  sail_assert (←((pure ((← readReg PSTATE).EL == EL3)) <||> (do
    (pure ((← readReg PSTATE).EL == EL2))))) "src/v8_base.sail:43830.46-43830.47"
  sail_assert (BEq.beq security SS_NonSecure) "src/v8_base.sail:43831.35-43831.36"
  let r ← (( do (undefined_TLBIRecord ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with address := (((Zeros (n := 24)) +++ (Sail.BitVec.extractLsb Rt 27 0)) +++ (Zeros (n := 12))) }
  let r : TLBIRecord := { r with ipaspace := PAS_NonSecure }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure ())

def __set_MPAM1_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM1_EL1_Type := value_name
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 54 (← (MPAM1_EL1_read ())) 0 (BitVec.slice r 0 54))))
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 5 (← (MPAM1_EL1_read ())) 55 (BitVec.slice r 55 5))))
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 2 (← (MPAM1_EL1_read ())) 61 (BitVec.slice r 61 2))))
  if (((! (HaveEL EL3)) && (! (HaveEL EL2))) : Bool)
  then (MPAM1_EL1_write (_update_MPAM1_EL1_Type_MPAMEN (← (MPAM1_EL1_read ())) (_get_MPAM1_EL1_Type_MPAMEN r)))
  else (pure ())

def MAIR0_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR0_Type := value_name
  if ((← (ELUsingAArch32 EL3)) : Bool)
  then (PRRR_NS_write (Mk_PRRR_Type (set_slice 32 (← (PRRR_NS_read ())) 0 (BitVec.slice r 0 32))))
  else
    (do
      if ((←((pure (! (HaveEL EL3))) <||> (do
           (pure (! (← (ELUsingAArch32 EL3))))))) : Bool)
      then writeReg MAIR_EL1 (Sail.BitVec.updateSubrange (← readReg MAIR_EL1) 31 0 (BitVec.slice r 0 32))
      else (PRRR_write (Mk_PRRR_Type (set_slice 32 (← (PRRR_read ())) 0 (BitVec.slice r 0 32)))))
  writeReg _MAIR0_NS r

def __set_SCTLR (value_name : (BitVec 32)) : SailM Unit := do
  let r : SCTLR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (__set_SCTLR_S r)
  else (__set_SCTLR_NS r)

def __set_CNTP_CTL (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTP_CTL_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (__set_CNTP_CTL_S r)
  else (__set_CNTP_CTL_NS r)

def MAIR1_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR1_Type := value_name
  if ((← (ELUsingAArch32 EL3)) : Bool)
  then (NMRR_NS_write (Mk_NMRR_Type (set_slice 32 (← (NMRR_NS_read ())) 0 (BitVec.slice r 0 32))))
  else
    (do
      if ((←((pure (! (HaveEL EL3))) <||> (do
           (pure (! (← (ELUsingAArch32 EL3))))))) : Bool)
      then writeReg MAIR_EL1 (Sail.BitVec.updateSubrange (← readReg MAIR_EL1) 63 32 (BitVec.slice r 0 32))
      else (NMRR_write (Mk_NMRR_Type (set_slice 32 (← (NMRR_read ())) 0 (BitVec.slice r 0 32)))))
  writeReg _MAIR1_NS r

def LR_read (_ : Unit) : SailM (BitVec 32) := do
  (R_read 14)
/-- Type quantifiers: k_N : Nat, k_illegal_psr_state : Bool, 31 < k_N -/
def SetPSTATEFromPSR__1 (spsr_in : (BitVec k_N)) (illegal_psr_state : Bool) : SailM Unit := do
  let spsr : (BitVec k_N) := spsr_in
  let from_aarch64 ← (( do (pure (! (← (UsingAArch32 ())))) ) : SailM Bool )
  writeReg PSTATE { (← readReg PSTATE) with SS := ← (do (DebugExceptionReturnSS spsr)) }
  writeReg ShouldAdvanceSS false
  if (illegal_psr_state : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with IL := 1#1 }
      if ((← (HaveSSBSExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with SSBS := ← (do (__UNKNOWN_bit ())) }
      else (pure ())
      if ((← (HaveBTIExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with BTYPE := ← (do (__UNKNOWN_bits 2)) }
      else (pure ())
      if ((← (HaveUAOExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with UAO := ← (do (__UNKNOWN_bit ())) }
      else (pure ())
      if ((← (HaveDITExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with DIT := ← (do (__UNKNOWN_bit ())) }
      else (pure ())
      if ((← (HaveMTEExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with TCO := ← (do (__UNKNOWN_bit ())) }
      else (pure ()))
  else
    (do
      sail_assert (20 <b (Sail.BitVec.length spsr_in)) "src/v8_base.sail:8854.34-8854.35"
      writeReg PSTATE { (← readReg PSTATE) with IL := (BitVec.join1 [(BitVec.access spsr 20)]) }
      if (((BitVec.join1 [(BitVec.access spsr 4)]) == 1#1) : Bool)
      then
        (do
          (AArch32_WriteMode (Sail.BitVec.extractLsb spsr 4 0))
          if ((← (HaveSSBSExt ())) : Bool)
          then
            (do
              sail_assert (23 <b (Sail.BitVec.length spsr_in)) "src/v8_base.sail:8859.42-8859.43"
              writeReg PSTATE { (← readReg PSTATE) with SSBS := (BitVec.join1 [(BitVec.access spsr 23)]) })
          else (pure ()))
      else
        (do
          writeReg PSTATE { (← readReg PSTATE) with nRW := 0#1 }
          writeReg PSTATE { (← readReg PSTATE) with EL := (Sail.BitVec.extractLsb spsr 3 2) }
          writeReg PSTATE { (← readReg PSTATE) with SP := (BitVec.join1 [(BitVec.access spsr 0)]) }
          if ((← (HaveBTIExt ())) : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with BTYPE := (Sail.BitVec.extractLsb spsr 11 10) }
          else (pure ())
          if ((← (HaveSSBSExt ())) : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with SSBS := (BitVec.join1 [(BitVec.access spsr 12)]) }
          else (pure ())
          if ((← (HaveUAOExt ())) : Bool)
          then
            (do
              sail_assert (23 <b (Sail.BitVec.length spsr_in)) "src/v8_base.sail:8874.42-8874.43"
              writeReg PSTATE { (← readReg PSTATE) with UAO := (BitVec.join1 [(BitVec.access spsr 23)]) })
          else (pure ())
          if ((← (HaveDITExt ())) : Bool)
          then
            (do
              sail_assert (24 <b (Sail.BitVec.length spsr_in)) "src/v8_base.sail:8878.42-8878.43"
              writeReg PSTATE { (← readReg PSTATE) with DIT := (BitVec.join1 [(BitVec.access spsr 24)]) })
          else (pure ())
          if ((← (HaveMTEExt ())) : Bool)
          then
            (do
              sail_assert (25 <b (Sail.BitVec.length spsr_in)) "src/v8_base.sail:8882.42-8882.43"
              writeReg PSTATE { (← readReg PSTATE) with TCO := (BitVec.join1 [(BitVec.access spsr 25)]) })
          else (pure ())
          if ((← (HaveGCS ())) : Bool)
          then
            (do
              sail_assert (34 <b (Sail.BitVec.length spsr_in)) "src/v8_base.sail:8886.42-8886.43"
              writeReg PSTATE { (← readReg PSTATE) with EXLOCK := (BitVec.join1 [(BitVec.access spsr 34)]) })
          else (pure ())))
  let spsr ← (( do
    if ((←((pure ((← readReg PSTATE).IL == 1#1)) <&&> (do
         (pure ((← readReg PSTATE).nRW == 1#1))))) : Bool)
    then
      (do
        if ((← (ConstrainUnpredictableBool Unpredictable_ILZEROT)) : Bool)
        then
          (do
            sail_assert (5 <b (Sail.BitVec.length spsr_in)) "src/v8_base.sail:8894.37-8894.38"
            (pure (BitVec.update spsr 5 (Bit 0#1))))
        else (pure spsr))
    else (pure spsr) ) : SailM (BitVec k_N) )
  let split_vec := (Sail.BitVec.extractLsb spsr 31 28)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  if ((← (HavePANExt ())) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with PAN := (BitVec.join1 [(BitVec.access spsr 22)]) }
  else (pure ())
  if (((← readReg PSTATE).nRW == 1#1) : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with Q := (BitVec.join1 [(BitVec.access spsr 27)]) }
      writeReg PSTATE { (← readReg PSTATE) with IT := ← (do (RestoredITBits spsr)) }
      writeReg ShouldAdvanceIT false
      if ((← (HaveDITExt ())) : Bool)
      then
        writeReg PSTATE { (← readReg PSTATE) with DIT := ← (do 
          if (((← (Restarting ())) || from_aarch64) : Bool)
          then (pure (BitVec.join1 [(BitVec.access spsr 24)]))
          else (pure (BitVec.join1 [(BitVec.access spsr 21)]))) }
      else (pure ())
      writeReg PSTATE { (← readReg PSTATE) with GE := (Sail.BitVec.extractLsb spsr 19 16) }
      writeReg PSTATE { (← readReg PSTATE) with E := (BitVec.join1 [(BitVec.access spsr 9)]) }
      let split_vec := (Sail.BitVec.extractLsb spsr 8 6)
      writeReg PSTATE { (← readReg PSTATE) with A := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb split_vec 0 0) }
      writeReg PSTATE { (← readReg PSTATE) with T := (BitVec.join1 [(BitVec.access spsr 5)]) })
  else
    (do
      if ((← (HaveFeatNMI ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with ALLINT := (BitVec.join1 [(BitVec.access spsr 13)]) }
      else (pure ())
      let split_vec := (Sail.BitVec.extractLsb spsr 9 6)
      writeReg PSTATE { (← readReg PSTATE) with D := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with A := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with I := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with F := (Sail.BitVec.extractLsb split_vec 0 0) })

def AArch64_CheckForWFxTrap (target_el : (BitVec 2)) (wfxtype : WFxType) : SailM Unit := do
  sail_assert (HaveEL target_el) "src/v8_base.sail:10675.28-10675.29"
  let is_wfe : Bool := ((BEq.beq wfxtype WFxType_WFE) || (BEq.beq wfxtype WFxType_WFET))
  let trap ← (( do (undefined_bool ()) ) : SailM Bool )
  let trap ← (( do
    let questionMark := target_el
    if ((questionMark == EL1) : Bool)
    then
      (do
        (pure ((← (do
              if (is_wfe : Bool)
              then (pure (_get_SCTLRType_nTWE (← (SCTLR_read__1 ()))))
              else (pure (_get_SCTLRType_nTWI (← (SCTLR_read__1 ())))))) == 0#1)))
    else
      (do
        if ((questionMark == EL2) : Bool)
        then
          (do
            (pure ((← (do
                  if (is_wfe : Bool)
                  then (pure (_get_HCR_EL2_Type_TWE (← readReg HCR_EL2)))
                  else (pure (_get_HCR_EL2_Type_TWI (← readReg HCR_EL2))))) == 1#1)))
        else
          (do
            if ((questionMark == EL3) : Bool)
            then
              (do
                (pure ((← (do
                      if (is_wfe : Bool)
                      then (pure (_get_SCR_EL3_Type_TWE (← readReg SCR_EL3)))
                      else (pure (_get_SCR_EL3_Type_TWI (← readReg SCR_EL3))))) == 1#1)))
            else (pure trap))) ) : SailM Bool )
  if (trap : Bool)
  then (AArch64_WFxTrap wfxtype target_el)
  else (pure ())

/-- Type quantifiers: N : Nat, k_fpexc : Bool, k_isbfloat16 : Bool, List.elem N [16, 32, 64] -/
def FPRoundBase__1 (op : real) (fpcr : (BitVec 64)) (rounding : FPRounding) (isbfloat16 : Bool) (fpexc : Bool) (N : Nat) : SailM (BitVec N) := SailME.run do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:15647.38-15647.39"
  sail_assert (bne op (0)) "src/v8_base.sail:15648.20-15648.21"
  sail_assert (bne rounding FPRounding_TIEAWAY) "src/v8_base.sail:15649.41-15649.42"
  let result ← (( do (undefined_bitvector N) ) : SailME (BitVec N) (BitVec N) )
  let minimum_exp ← (( do (undefined_int ()) ) : SailME (BitVec N) Int )
  let F : Nat := 7
  let E : Nat := 5
  let (E, F, minimum_exp) : (Int × Int × Int) :=
    if ((N == 16) : Bool)
    then
      (let minimum_exp : Int := (Neg.neg 14)
      let E : Nat := 5
      let F : Nat := 10
      (E, F, minimum_exp))
    else
      (let (E, F, minimum_exp) : (Int × Int × Int) :=
        if (((N == 32) && isbfloat16) : Bool)
        then
          (let minimum_exp : Int := (Neg.neg 126)
          let E : Nat := 8
          let F : Nat := 7
          (E, F, minimum_exp))
        else
          (let (E, F, minimum_exp) : (Int × Int × Int) :=
            if ((N == 32) : Bool)
            then
              (let minimum_exp : Int := (Neg.neg 126)
              let E : Nat := 8
              let F : Nat := 23
              (E, F, minimum_exp))
            else
              (let minimum_exp : Int := (Neg.neg 1022)
              let E : Nat := 11
              let F : Nat := 52
              (E, F, minimum_exp))
          (E, F, minimum_exp))
      (E, F, minimum_exp))
  let minimum_exp := minimum_exp
  let F := F
  let E := E
  let sign ← (( do (undefined_bitvector 1) ) : SailME (BitVec N) (BitVec 1) )
  let mantissa ← (( do (undefined_real ()) ) : SailME (BitVec N) real )
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
    (pure loop_vars) ) : SailME (BitVec N) (Int × real) )
  let (exponent, mantissa) ← (( do
    let mut loop_vars_1 := (exponent, mantissa)
    while (λ (exponent, mantissa) => (gteq_real mantissa (2))) loop_vars_1 do
      let (exponent, mantissa) := loop_vars_1
      loop_vars_1 :=
        (let mantissa : real := (div_real mantissa (2))
        let exponent : Int := (exponent +i 1)
        (exponent, mantissa) : (Int × real))
    (pure loop_vars_1) ) : SailME (BitVec N) (Int × real) )
  let exponent := exponent
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailME (BitVec N) Bool )
  if ((((! altfp) && ((((_get_FPCRType_FZ fpcr) == 1#1) && (N != 16)) || (((_get_FPCRType_FZ16 fpcr) == 1#1) && (N == 16)))) && (exponent <b minimum_exp)) : Bool)
  then
    (do
      if ((← (UsingAArch32 ())) : Bool)
      then (FPSCR_write (_update_FPSCR_Type_UFC (← (FPSCR_read__1 ())) 1#1))
      else
        (do
          if (fpexc : Bool)
          then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 3 3 1#1)
          else (pure ()))
      (FPZero sign N))
  else
    (do
      let biased_exp_unconstrained : Int := ((exponent -i minimum_exp) +i 1)
      let int_mant_unconstrained : Int := (round_down (mult_real mantissa (real_power (2) F)))
      let error_unconstrained : real := (sub_real (mult_real mantissa (real_power (2) F)) (to_real int_mant_unconstrained))
      let biased_exp : Int := (Max.max ((exponent -i minimum_exp) +i 1) 0)
      let mantissa : real :=
        if ((biased_exp == 0) : Bool)
        then (div_real mantissa (real_power (2) (minimum_exp -i exponent)))
        else mantissa
      let mantissa := mantissa
      let int_mant : Int := (round_down (mult_real mantissa (real_power (2) F)))
      let error : real := (sub_real (mult_real mantissa (real_power (2) F)) (to_real int_mant))
      let trapped_UF ← (( do (pure ((_get_FPCRType_UFE fpcr) == 1#1)) <&&> (do (pure (! (← (InStreamingMode ())))) <||> (do (IsFullA64Enabled ()))) ) : SailME (BitVec N) Bool )
      if ((((! altfp) && (biased_exp == 0)) && ((bne error (0)) || trapped_UF)) : Bool)
      then
        (do
          if (fpexc : Bool)
          then (FPProcessException FPExc_Underflow fpcr)
          else (pure ()))
      else (pure ())
      let round_up_unconstrained ← (( do (undefined_bool ()) ) : SailME (BitVec N) Bool )
      let round_up ← (( do (undefined_bool ()) ) : SailME (BitVec N) Bool )
      let overflow_to_inf ← (( do (undefined_bool ()) ) : SailME (BitVec N) Bool )
      let (overflow_to_inf, round_up) ← (( do
        if (altfp : Bool)
        then
          (do
            let (overflow_to_inf, round_up, round_up_unconstrained) : (Bool × Bool × Bool) :=
              match rounding with
              | .FPRounding_TIEEVEN =>
                (let round_up_unconstrained : Bool := ((gt_real error_unconstrained (1/2)) || ((eq_real error_unconstrained (1/2)) && ((BitVec.join1 [(integer_access int_mant_unconstrained 0)]) == 1#1)))
                let round_up : Bool := ((gt_real error (1/2)) || ((eq_real error (1/2)) && ((BitVec.join1 [(integer_access int_mant 0)]) == 1#1)))
                let overflow_to_inf : Bool := true
                (overflow_to_inf, round_up, round_up_unconstrained))
              | .FPRounding_POSINF =>
                (let round_up_unconstrained : Bool := ((bne error_unconstrained (0)) && (sign == 0#1))
                let round_up : Bool := ((bne error (0)) && (sign == 0#1))
                let overflow_to_inf : Bool := (sign == 0#1)
                (overflow_to_inf, round_up, round_up_unconstrained))
              | .FPRounding_NEGINF =>
                (let round_up_unconstrained : Bool := ((bne error_unconstrained (0)) && (sign == 1#1))
                let round_up : Bool := ((bne error (0)) && (sign == 1#1))
                let overflow_to_inf : Bool := (sign == 1#1)
                (overflow_to_inf, round_up, round_up_unconstrained))
              | .FPRounding_ZERO =>
                (let round_up_unconstrained : Bool := false
                let round_up : Bool := false
                let overflow_to_inf : Bool := false
                (overflow_to_inf, round_up, round_up_unconstrained))
              | .FPRounding_ODD =>
                (let round_up_unconstrained : Bool := false
                let round_up : Bool := false
                let overflow_to_inf : Bool := false
                (overflow_to_inf, round_up, round_up_unconstrained))
              | _ => (overflow_to_inf, round_up, round_up_unconstrained)
            let (biased_exp_unconstrained, int_mant_unconstrained) : (Int × Int) :=
              if (round_up_unconstrained : Bool)
              then
                (let int_mant_unconstrained : Int := (int_mant_unconstrained +i 1)
                let (biased_exp_unconstrained, int_mant_unconstrained) : (Int × Int) :=
                  if ((int_mant_unconstrained == (2 ^i (F +i 1))) : Bool)
                  then
                    (let biased_exp_unconstrained : Int := (biased_exp_unconstrained +i 1)
                    let int_mant_unconstrained : Int := (fdiv_int int_mant_unconstrained 2)
                    (biased_exp_unconstrained, int_mant_unconstrained))
                  else (biased_exp_unconstrained, int_mant_unconstrained)
                (biased_exp_unconstrained, int_mant_unconstrained))
              else (biased_exp_unconstrained, int_mant_unconstrained)
            let int_mant_unconstrained := int_mant_unconstrained
            let biased_exp_unconstrained := biased_exp_unconstrained
            if (((biased_exp_unconstrained <b 1) && (int_mant_unconstrained != 0)) : Bool)
            then
              (do
                if (((((_get_FPCRType_FZ fpcr) == 1#1) && (N != 16)) || (((_get_FPCRType_FZ16 fpcr) == 1#1) && (N == 16))) : Bool)
                then
                  SailME.throw (← (do
                      if (fpexc : Bool)
                      then
                        (do
                          writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 3 3 1#1)
                          (FPProcessException FPExc_Inexact fpcr))
                      else (pure ())
                      (FPZero sign N)))
                else
                  (do
                    if (((bne error (0)) || trapped_UF) : Bool)
                    then
                      (do
                        if (fpexc : Bool)
                        then (FPProcessException FPExc_Underflow fpcr)
                        else (pure ()))
                    else (pure ())))
            else (pure ())
            (pure (overflow_to_inf, round_up)))
        else
          (let (overflow_to_inf, round_up) : (Bool × Bool) :=
            match rounding with
            | .FPRounding_TIEEVEN =>
              (let round_up : Bool := ((gt_real error (1/2)) || ((eq_real error (1/2)) && ((BitVec.join1 [(integer_access int_mant 0)]) == 1#1)))
              let overflow_to_inf : Bool := true
              (overflow_to_inf, round_up))
            | .FPRounding_POSINF =>
              (let round_up : Bool := ((bne error (0)) && (sign == 0#1))
              let overflow_to_inf : Bool := (sign == 0#1)
              (overflow_to_inf, round_up))
            | .FPRounding_NEGINF =>
              (let round_up : Bool := ((bne error (0)) && (sign == 1#1))
              let overflow_to_inf : Bool := (sign == 1#1)
              (overflow_to_inf, round_up))
            | .FPRounding_ZERO =>
              (let round_up : Bool := false
              let overflow_to_inf : Bool := false
              (overflow_to_inf, round_up))
            | .FPRounding_ODD =>
              (let round_up : Bool := false
              let overflow_to_inf : Bool := false
              (overflow_to_inf, round_up))
            | _ => (overflow_to_inf, round_up)
          (pure (overflow_to_inf, round_up))) ) : SailME (BitVec N) (Bool × Bool) )
      let (biased_exp, int_mant) : (Int × Int) :=
        if (round_up : Bool)
        then
          (let int_mant : Int := (int_mant +i 1)
          let biased_exp : Int :=
            if ((int_mant == (2 ^i F)) : Bool)
            then 1
            else biased_exp
          let (biased_exp, int_mant) : (Int × Int) :=
            if ((int_mant == (2 ^i (F +i 1))) : Bool)
            then
              (let biased_exp : Int := (biased_exp +i 1)
              let int_mant : Int := (fdiv_int int_mant 2)
              (biased_exp, int_mant))
            else (biased_exp, int_mant)
          (biased_exp, int_mant))
        else (biased_exp, int_mant)
      let biased_exp := biased_exp
      let int_mant : Int :=
        if (((bne error (0)) && (BEq.beq rounding FPRounding_ODD)) : Bool)
        then (integer_update_subrange int_mant 0 0 1#1)
        else int_mant
      let int_mant := int_mant
      let (error, result) ← (( do
        if (((N != 16) || ((_get_FPCRType_AHP fpcr) == 0#1)) : Bool)
        then
          (do
            let (error, result) ← (( do
              if ((biased_exp ≥b ((2 ^i E) -i 1)) : Bool)
              then
                (do
                  let result ←
                    if (overflow_to_inf : Bool)
                    then (FPInfinity sign N)
                    else (FPMaxNormal sign N)
                  if (fpexc : Bool)
                  then (FPProcessException FPExc_Overflow fpcr)
                  else (pure ())
                  let error : real := (1)
                  (pure (error, result)))
              else
                (do
                  sail_assert ((N -i ((E +i F) +i 1)) ≥b 0) "src/v8_base.sail:15829.54-15829.55"
                  let result : (BitVec N) := (((sign +++ (integer_subrange biased_exp (E -i 1) 0)) +++ (integer_subrange int_mant (F -i 1) 0)) +++ (Zeros (n := (N -i ((E +i F) +i 1)))))
                  (pure (error, result))) ) : SailME (BitVec N) (real × (BitVec N)) )
            (pure (error, result)))
        else
          (do
            let (error, result) ← (( do
              if ((biased_exp ≥b (2 ^i E)) : Bool)
              then
                (do
                  let result : (BitVec N) := (sign +++ (Ones (n := (N -i 1))))
                  if (fpexc : Bool)
                  then (FPProcessException FPExc_InvalidOp fpcr)
                  else (pure ())
                  let error : real := (0)
                  (pure (error, result)))
              else
                (do
                  sail_assert ((N -i ((E +i F) +i 1)) ≥b 0) "src/v8_base.sail:15840.54-15840.55"
                  let result : (BitVec N) := (((sign +++ (integer_subrange biased_exp (E -i 1) 0)) +++ (integer_subrange int_mant (F -i 1) 0)) +++ (Zeros (n := (N -i ((E +i F) +i 1)))))
                  (pure (error, result))) ) : SailME (BitVec N) (real × (BitVec N)) )
            (pure (error, result))) ) : SailME (BitVec N) (real × (BitVec N)) )
      if ((bne error (0)) : Bool)
      then
        (do
          if (fpexc : Bool)
          then (FPProcessException FPExc_Inexact fpcr)
          else (pure ()))
      else (pure ())
      (pure result))

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_isbfloat16 : Bool, List.elem k_N [16, 32, 64] -/
def FPUnpackBase__1 (fpval : (BitVec k_N)) (fpcr_in : (BitVec 64)) (fpexc : Bool) (isbfloat16 : Bool) : SailM (FPType × (BitVec 1) × real) := do
  let exp16 ← (( do (undefined_bitvector 5) ) : SailM (BitVec 5) )
  let exp64 ← (( do (undefined_bitvector 11) ) : SailM (BitVec 11) )
  let frac16 ← (( do (undefined_bitvector 10) ) : SailM (BitVec 10) )
  let frac64 ← (( do (undefined_bitvector 52) ) : SailM (BitVec 52) )
  sail_assert (((Sail.BitVec.length fpval) == 16) || (((Sail.BitVec.length fpval) == 32) || ((Sail.BitVec.length fpval) == 64))) "src/v8_base.sail:15949.41-15949.42"
  let fpcr : FPCRType := fpcr_in
  let altfp ← (( do (HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))) ) : SailM Bool )
  let fiz : Bool := (altfp && ((_get_FPCRType_FIZ fpcr) == 1#1))
  let fz : Bool := (((_get_FPCRType_FZ fpcr) == 1#1) && (! (altfp && ((_get_FPCRType_AH fpcr) == 1#1))))
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let fptype ← (( do (undefined_FPType ()) ) : SailM FPType )
  let (fptype, sign, value_name) ← (( do
    if ((((Sail.BitVec.length fpval) == 16) && (! isbfloat16)) : Bool)
    then
      (let sign : (BitVec 1) := (BitVec.join1 [(BitVec.access fpval 15)])
      let exp16 : (BitVec 5) := (Sail.BitVec.extractLsb fpval 14 10)
      let frac16 : (BitVec 10) := (Sail.BitVec.extractLsb fpval 9 0)
      let (fptype, value_name) : (FPType × real) :=
        if ((IsZero exp16) : Bool)
        then
          (let (fptype, value_name) : (FPType × real) :=
            if (((IsZero frac16) || ((_get_FPCRType_FZ16 fpcr) == 1#1)) : Bool)
            then
              (let fptype : FPType := FPType_Zero
              let value_name : real := (0)
              (fptype, value_name))
            else
              (let fptype : FPType := FPType_Denormal
              let value_name : real := (mult_real (real_power (2) (Neg.neg 14)) (mult_real (to_real (BitVec.toNat frac16)) (real_power (2) (Neg.neg 10))))
              (fptype, value_name))
          (fptype, value_name))
        else
          (let (fptype, value_name) : (FPType × real) :=
            if (((IsOnes exp16) && ((_get_FPCRType_AHP fpcr) == 0#1)) : Bool)
            then
              (let (fptype, value_name) : (FPType × real) :=
                if ((IsZero frac16) : Bool)
                then
                  (let fptype : FPType := FPType_Infinity
                  let value_name : real := (real_power (2) 1000000)
                  (fptype, value_name))
                else
                  (let fptype : FPType :=
                    if (((BitVec.join1 [(BitVec.access frac16 9)]) == 1#1) : Bool)
                    then FPType_QNaN
                    else FPType_SNaN
                  let value_name : real := (0)
                  (fptype, value_name))
              (fptype, value_name))
            else
              (let fptype : FPType := FPType_Nonzero
              let value_name : real := (mult_real (real_power (2) ((BitVec.toNat exp16) -i 15)) (add_real (1) (mult_real (to_real (BitVec.toNat frac16)) (real_power (2) (Neg.neg 10)))))
              (fptype, value_name))
          (fptype, value_name))
      (pure (fptype, sign, value_name)))
    else
      (do
        let (fptype, sign, value_name) ← (( do
          if ((((Sail.BitVec.length fpval) == 32) || isbfloat16) : Bool)
          then
            (do
              let exp32 ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
              let frac32 ← (( do (undefined_bitvector 23) ) : SailM (BitVec 23) )
              let (exp32, frac32, sign) : ((BitVec 8) × (BitVec 23) × (BitVec 1)) :=
                if (isbfloat16 : Bool)
                then
                  (let sign : (BitVec 1) := (BitVec.join1 [(BitVec.access fpval 15)])
                  let exp32 : (BitVec 8) := (Sail.BitVec.extractLsb fpval 14 7)
                  let frac32 : (BitVec 23) := ((Sail.BitVec.extractLsb fpval 6 0) +++ (Zeros (n := 16)))
                  (exp32, frac32, sign))
                else
                  (let sign : (BitVec 1) := (BitVec.join1 [(BitVec.access fpval 31)])
                  let exp32 : (BitVec 8) := (Sail.BitVec.extractLsb fpval 30 23)
                  let frac32 : (BitVec 23) := (Sail.BitVec.extractLsb fpval 22 0)
                  (exp32, frac32, sign))
              let (fptype, value_name) ← (( do
                if ((IsZero exp32) : Bool)
                then
                  (do
                    let (fptype, value_name) ← (( do
                      if ((IsZero frac32) : Bool)
                      then
                        (let fptype : FPType := FPType_Zero
                        let value_name : real := (0)
                        (pure (fptype, value_name)))
                      else
                        (do
                          let (fptype, value_name) ← (( do
                            if ((fz || fiz) : Bool)
                            then
                              (do
                                let fptype : FPType := FPType_Zero
                                let value_name : real := (0)
                                if (fz : Bool)
                                then
                                  (do
                                    if (fpexc : Bool)
                                    then (FPProcessException FPExc_InputDenorm fpcr)
                                    else (pure ()))
                                else (pure ())
                                (pure (fptype, value_name)))
                            else
                              (let fptype : FPType := FPType_Denormal
                              let value_name : real := (mult_real (real_power (2) (Neg.neg 126)) (mult_real (to_real (BitVec.toNat frac32)) (real_power (2) (Neg.neg 23))))
                              (pure (fptype, value_name))) ) : SailM (FPType × real) )
                          (pure (fptype, value_name))) ) : SailM (FPType × real) )
                    (pure (fptype, value_name)))
                else
                  (let (fptype, value_name) : (FPType × real) :=
                    if ((IsOnes exp32) : Bool)
                    then
                      (let (fptype, value_name) : (FPType × real) :=
                        if ((IsZero frac32) : Bool)
                        then
                          (let fptype : FPType := FPType_Infinity
                          let value_name : real := (real_power (2) 1000000)
                          (fptype, value_name))
                        else
                          (let fptype : FPType :=
                            if (((BitVec.join1 [(BitVec.access frac32 22)]) == 1#1) : Bool)
                            then FPType_QNaN
                            else FPType_SNaN
                          let value_name : real := (0)
                          (fptype, value_name))
                      (fptype, value_name))
                    else
                      (let fptype : FPType := FPType_Nonzero
                      let value_name : real := (mult_real (real_power (2) ((BitVec.toNat exp32) -i 127)) (add_real (1) (mult_real (to_real (BitVec.toNat frac32)) (real_power (2) (Neg.neg 23)))))
                      (fptype, value_name))
                  (pure (fptype, value_name))) ) : SailM (FPType × real) )
              (pure (fptype, sign, value_name)))
          else
            (do
              let sign : (BitVec 1) := (BitVec.join1 [(BitVec.access fpval 63)])
              let exp64 : (BitVec 11) := (Sail.BitVec.extractLsb fpval 62 52)
              let frac64 : (BitVec 52) := (Sail.BitVec.extractLsb fpval 51 0)
              let (fptype, value_name) ← (( do
                if ((IsZero exp64) : Bool)
                then
                  (do
                    let (fptype, value_name) ← (( do
                      if ((IsZero frac64) : Bool)
                      then
                        (let fptype : FPType := FPType_Zero
                        let value_name : real := (0)
                        (pure (fptype, value_name)))
                      else
                        (do
                          let (fptype, value_name) ← (( do
                            if ((fz || fiz) : Bool)
                            then
                              (do
                                let fptype : FPType := FPType_Zero
                                let value_name : real := (0)
                                if (fz : Bool)
                                then
                                  (do
                                    if (fpexc : Bool)
                                    then (FPProcessException FPExc_InputDenorm fpcr)
                                    else (pure ()))
                                else (pure ())
                                (pure (fptype, value_name)))
                            else
                              (let fptype : FPType := FPType_Denormal
                              let value_name : real := (mult_real (real_power (2) (Neg.neg 1022)) (mult_real (to_real (BitVec.toNat frac64)) (real_power (2) (Neg.neg 52))))
                              (pure (fptype, value_name))) ) : SailM (FPType × real) )
                          (pure (fptype, value_name))) ) : SailM (FPType × real) )
                    (pure (fptype, value_name)))
                else
                  (let (fptype, value_name) : (FPType × real) :=
                    if ((IsOnes exp64) : Bool)
                    then
                      (let (fptype, value_name) : (FPType × real) :=
                        if ((IsZero frac64) : Bool)
                        then
                          (let fptype : FPType := FPType_Infinity
                          let value_name : real := (real_power (2) 1000000)
                          (fptype, value_name))
                        else
                          (let fptype : FPType :=
                            if (((BitVec.join1 [(BitVec.access frac64 51)]) == 1#1) : Bool)
                            then FPType_QNaN
                            else FPType_SNaN
                          let value_name : real := (0)
                          (fptype, value_name))
                      (fptype, value_name))
                    else
                      (let fptype : FPType := FPType_Nonzero
                      let value_name : real := (mult_real (real_power (2) ((BitVec.toNat exp64) -i 1023)) (add_real (1) (mult_real (to_real (BitVec.toNat frac64)) (real_power (2) (Neg.neg 52)))))
                      (fptype, value_name))
                  (pure (fptype, value_name))) ) : SailM (FPType × real) )
              (pure (fptype, sign, value_name))) ) : SailM (FPType × (BitVec 1) × real) )
        (pure (fptype, sign, value_name))) ) : SailM (FPType × (BitVec 1) × real) )
  let value_name : real :=
    if ((sign == 1#1) : Bool)
    then (neg_real value_name)
    else value_name
  let value_name := value_name
  (pure (fptype, sign, value_name))

/-- Type quantifiers: N : Int -/
def FPProcessDenorms (type1 : FPType) (type2 : FPType) (N : Int) (fpcr : (BitVec 64)) : SailM Unit := do
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  if (((altfp && (N != 16)) && ((BEq.beq type1 FPType_Denormal) || (BEq.beq type2 FPType_Denormal))) : Bool)
  then (FPProcessException FPExc_InputDenorm fpcr)
  else (pure ())

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPProcessNaN__1 (fptype : FPType) (op : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:16162.41-16162.42"
  sail_assert ((BEq.beq fptype FPType_QNaN) || (BEq.beq fptype FPType_SNaN)) "src/v8_base.sail:16163.56-16163.57"
  let topfrac : Nat := 9
  let topfrac : Int :=
    match (Sail.BitVec.length op) with
    | 16 => 9
    | 32 => 22
    | 64 => 51
    | _ => topfrac
  let topfrac := topfrac
  let result : (BitVec k_N) := op
  let result ← (( do
    if ((BEq.beq fptype FPType_SNaN) : Bool)
    then
      (do
        sail_assert ((0 ≤b topfrac) && (topfrac <b (Sail.BitVec.length result))) "src/v8_base.sail:16180.58-16180.59"
        let result : (BitVec k_N) := (BitVec.update result topfrac (Bit 1#1))
        if (fpexc : Bool)
        then (FPProcessException FPExc_InvalidOp fpcr)
        else (pure ())
        (pure result))
    else (pure result) ) : SailM (BitVec k_N) )
  if (((_get_FPCRType_DN fpcr) == 1#1) : Bool)
  then (do (FPDefaultNaN__1 fpcr (Sail.BitVec.length result)))
  else (pure result)

/-- Type quantifiers: N : Int -/
def FPProcessDenorm (fptype : FPType) (N : Int) (fpcr : (BitVec 64)) : SailM Unit := do
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  if (((altfp && (N != 16)) && (BEq.beq fptype FPType_Denormal)) : Bool)
  then (FPProcessException FPExc_InputDenorm fpcr)
  else (pure ())

/-- Type quantifiers: N : Int -/
def FPProcessDenorms3 (type1 : FPType) (type2 : FPType) (type3 : FPType) (N : Int) (fpcr : (BitVec 64)) : SailM Unit := do
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  if (((altfp && (N != 16)) && (((BEq.beq type1 FPType_Denormal) || (BEq.beq type2 FPType_Denormal)) || (BEq.beq type3 FPType_Denormal))) : Bool)
  then (FPProcessException FPExc_InputDenorm fpcr)
  else (pure ())

/-- Type quantifiers: k_size : Nat, k_size ≥ 0 -/
def MemAtomicRCW (address : (BitVec 64)) (cmpoperand : (BitVec k_size)) (operand : (BitVec k_size)) (accdesc_in : AccessDescriptor) : SailM ((BitVec 4) × (BitVec k_size)) := do
  sail_assert accdesc_in.atomicop "src/v8_base.sail:28582.30-28582.31"
  sail_assert accdesc_in.rcw "src/v8_base.sail:28583.25-28583.26"
  let bytes := (Int.ediv (Sail.BitVec.length operand) 8)
  sail_assert ((bytes == 8) || (bytes == 16)) "src/v8_base.sail:28585.35-28585.36"
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let oldvalue ← (( do (undefined_bitvector (Sail.BitVec.length operand)) ) : SailM (BitVec k_size) )
  let newvalue ← (( do (undefined_bitvector (Sail.BitVec.length operand)) ) : SailM (BitVec k_size) )
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address bytes)
  let accdesc ← (( do
    if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
    then (do (pure { accdesc with tagchecked := ← (do (AArch64_AccessIsTagChecked address accdesc)) }))
    else (pure accdesc) ) : SailM AccessDescriptor )
  if ((←((pure (! aligned)) <&&> (do
       (AArch64_UnalignedAccessFaults accdesc address bytes)))) : Bool)
  then (AArch64_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned (Sail.BitVec.length operand)) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then (AArch64_Abort address memaddrdesc.fault)
  else (pure ())
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) (Sail.BitVec.length operand))
    else ()
  if ((←((pure ((← (HaveMTE2Ext ())) && accdesc.tagchecked)) <&&> (do
       (pure (! (← (HaveMTEStoreOnlyExt ())))) <||> (do
         (pure (! (← (StoreOnlyTagCheckingEnabled accdesc.el)))))))) : Bool)
  then
    (do
      let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
      if ((! (← (AArch64_CheckTag memaddrdesc accdesc ptag))) : Bool)
      then (AArch64_TagCheckFault address accdesc)
      else (pure ()))
  else (pure ())
  let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
  sail_assert ((8 *i bytes) == (Sail.BitVec.length operand)) "src/v8_base.sail:28612.42-28612.43"
  let (memstatus, oldvalue) ← (( do
    let (tup__0, tup__1) ← do (PhysMemRead memaddrdesc bytes accdesc none)
    let memstatus : PhysMemRetStatus := tup__0
    let oldvalue : (BitVec k_size) := tup__1
    (pure (memstatus, oldvalue)) ) : SailM (PhysMemRetStatus × (BitVec k_size)) )
  if ((IsFault__2 memstatus) : Bool)
  then (HandleExternalReadAbort memstatus memaddrdesc bytes accdesc)
  else (pure ())
  let oldvalue ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (reverse_endianness oldvalue))
    else (pure oldvalue) ) : SailM (BitVec k_size) )
  let oldvalue := oldvalue
  let cmpfail : Bool := false
  let (cmpfail, newvalue) : (Bool × (BitVec k_size)) :=
    match accdesc.modop with
    | .MemAtomicOp_BIC =>
      (let newvalue : (BitVec k_size) := (oldvalue &&& (Complement.complement operand))
      (cmpfail, newvalue))
    | .MemAtomicOp_ORR =>
      (let newvalue : (BitVec k_size) := (oldvalue ||| operand)
      (cmpfail, newvalue))
    | .MemAtomicOp_SWP =>
      (let newvalue : (BitVec k_size) := operand
      (cmpfail, newvalue))
    | .MemAtomicOp_CAS =>
      (let newvalue : (BitVec k_size) := operand
      let cmpfail : Bool := (oldvalue != cmpoperand)
      (cmpfail, newvalue))
    | _ => (cmpfail, newvalue)
  let nzcv ← (( do
    if (cmpfail : Bool)
    then (pure 0b1010#4)
    else (do (RCWCheck oldvalue newvalue accdesc.rcws)) ) : SailM (BitVec 4) )
  let accdesc ← (( do
    if ((←((HaveMTEStoreOnlyExt ()) <&&> (do
         (StoreOnlyTagCheckingEnabled accdesc.el)))) : Bool)
    then
      (do
        let accdesc ← (( do
          if ((accdesc.tagchecked && cmpfail) : Bool)
          then (do (pure { accdesc with tagchecked := ← (do (ConstrainUnpredictableBool Unpredictable_STOREONLYTAGCHECKEDCAS)) }))
          else (pure accdesc) ) : SailM AccessDescriptor )
        if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
        then
          (do
            let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
            if ((! (← (AArch64_CheckTag memaddrdesc accdesc ptag))) : Bool)
            then
              (do
                let accdesc : AccessDescriptor := { accdesc with read := false }
                (AArch64_TagCheckFault address accdesc)
                (pure accdesc))
            else (pure accdesc))
        else (pure accdesc))
    else (pure accdesc) ) : SailM AccessDescriptor )
  if ((nzcv == 0b0010#4) : Bool)
  then
    (do
      let newvalue ← (( do
        if ((← (BigEndian accdesc.acctype)) : Bool)
        then (pure (reverse_endianness newvalue))
        else (pure newvalue) ) : SailM (BitVec k_size) )
      let memstatus ← (( do (PhysMemWrite memaddrdesc bytes accdesc none newvalue) ) : SailM PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then (HandleExternalWriteAbort memstatus memaddrdesc bytes accdesc)
      else (pure ()))
  else (pure ())
  (pure (nzcv, oldvalue))

def CheckOriginalSVEEnabled (_ : Unit) : SailM Unit := do
  sail_assert (← (HaveSVE ())) "src/v8_base.sail:29250.20-29250.21"
  let disabled ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((←((pure (HaveEL EL3)) <&&> (do
       (pure ((_get_CPTR_EL3_Type_EZ (← readReg CPTR_EL3)) == 0#1)) <||> (do
         (pure ((_get_CPTR_EL3_Type_TFP (← readReg CPTR_EL3)) == 1#1)))) <&&> (do
       (EL3SDDUndefPriority ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let disabled ← (( do
    if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
         (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
         (pure (! (← (IsInHost ()))))))) : Bool)
    then
      (do
        let disabled ← (( do
          let b__0 ← do (pure (_get_CPACR_EL1_Type_ZEN (← readReg CPACR_EL1)))
          if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
          then (pure true)
          else
            (do
              if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
              then (do (pure ((← readReg PSTATE).EL == EL0)))
              else (pure false)) ) : SailM Bool )
        if (disabled : Bool)
        then (SVEAccessTrap EL1)
        else (pure ())
        let disabled ← (( do
          let b__2 ← do (pure (_get_CPACR_EL1_Type_FPEN (← readReg CPACR_EL1)))
          if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
          then (pure true)
          else
            (do
              if ((b__2 == (0b01#2 : (BitVec 2))) : Bool)
              then (do (pure ((← readReg PSTATE).EL == EL0)))
              else (pure false)) ) : SailM Bool )
        if (disabled : Bool)
        then (AArch64_AdvSIMDFPAccessTrap EL1)
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
            let b__4 ← do (pure (_get_CPTR_EL2_Type_ZEN (← readReg CPTR_EL2)))
            if (((Sail.BitVec.extractLsb b__4 0 0) == (0#1 : (BitVec 1))) : Bool)
            then (pure true)
            else
              (do
                if ((b__4 == (0b01#2 : (BitVec 2))) : Bool)
                then (do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))
                else (pure false)) ) : SailM Bool )
          if (disabled : Bool)
          then (SVEAccessTrap EL2)
          else (pure ())
          let disabled ← (( do
            let b__6 ← do (pure (_get_CPTR_EL2_Type_FPEN (← readReg CPTR_EL2)))
            if (((Sail.BitVec.extractLsb b__6 0 0) == (0#1 : (BitVec 1))) : Bool)
            then (pure true)
            else
              (do
                if ((b__6 == (0b01#2 : (BitVec 2))) : Bool)
                then (do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))
                else (pure false)) ) : SailM Bool )
          if (disabled : Bool)
          then (AArch64_AdvSIMDFPAccessTrap EL2)
          else (pure ()))
      else
        (do
          if (((_get_CPTR_EL2_Type_TZ (← readReg CPTR_EL2)) == 1#1) : Bool)
          then (SVEAccessTrap EL2)
          else (pure ())
          if (((_get_CPTR_EL2_Type_TFP (← readReg CPTR_EL2)) == 1#1) : Bool)
          then (AArch64_AdvSIMDFPAccessTrap EL2)
          else (pure ())))
  else (pure ())
  if ((HaveEL EL3) : Bool)
  then
    (do
      if (((_get_CPTR_EL3_Type_EZ (← readReg CPTR_EL3)) == 0#1) : Bool)
      then
        (do
          if ((← (EL3SDDUndef ())) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (SVEAccessTrap EL3))
      else (pure ())
      if (((_get_CPTR_EL3_Type_TFP (← readReg CPTR_EL3)) == 1#1) : Bool)
      then
        (do
          if ((← (EL3SDDUndef ())) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (AArch64_AdvSIMDFPAccessTrap EL3))
      else (pure ()))
  else (pure ())

def CheckSMEEnabled (_ : Unit) : SailM Unit := do
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
        let disabled ← (( do
          let b__2 ← do (pure (_get_CPACR_EL1_Type_FPEN (← readReg CPACR_EL1)))
          if (((Sail.BitVec.extractLsb b__2 0 0) == (0#1 : (BitVec 1))) : Bool)
          then (pure true)
          else
            (do
              if ((b__2 == (0b01#2 : (BitVec 2))) : Bool)
              then (do (pure ((← readReg PSTATE).EL == EL0)))
              else (pure false)) ) : SailM Bool )
        if (disabled : Bool)
        then (AArch64_AdvSIMDFPAccessTrap EL1)
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
            let b__4 ← do (pure (_get_CPTR_EL2_Type_SMEN (← readReg CPTR_EL2)))
            if (((Sail.BitVec.extractLsb b__4 0 0) == (0#1 : (BitVec 1))) : Bool)
            then (pure true)
            else
              (do
                if ((b__4 == (0b01#2 : (BitVec 2))) : Bool)
                then (do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))
                else (pure false)) ) : SailM Bool )
          if (disabled : Bool)
          then (SMEAccessTrap SMEExceptionType_AccessTrap EL2)
          else (pure ())
          let disabled ← (( do
            let b__6 ← do (pure (_get_CPTR_EL2_Type_FPEN (← readReg CPTR_EL2)))
            if (((Sail.BitVec.extractLsb b__6 0 0) == (0#1 : (BitVec 1))) : Bool)
            then (pure true)
            else
              (do
                if ((b__6 == (0b01#2 : (BitVec 2))) : Bool)
                then (do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))
                else (pure false)) ) : SailM Bool )
          if (disabled : Bool)
          then (AArch64_AdvSIMDFPAccessTrap EL2)
          else (pure ()))
      else
        (do
          if (((_get_CPTR_EL2_Type_TSM (← readReg CPTR_EL2)) == 1#1) : Bool)
          then (SMEAccessTrap SMEExceptionType_AccessTrap EL2)
          else (pure ())
          if (((_get_CPTR_EL2_Type_TFP (← readReg CPTR_EL2)) == 1#1) : Bool)
          then (AArch64_AdvSIMDFPAccessTrap EL2)
          else (pure ())))
  else (pure ())
  if ((HaveEL EL3) : Bool)
  then
    (do
      if (((_get_CPTR_EL3_Type_ESM (← readReg CPTR_EL3)) == 0#1) : Bool)
      then (SMEAccessTrap SMEExceptionType_AccessTrap EL3)
      else (pure ())
      if (((_get_CPTR_EL3_Type_TFP (← readReg CPTR_EL3)) == 1#1) : Bool)
      then (AArch64_AdvSIMDFPAccessTrap EL3)
      else (pure ()))
  else (pure ())

def SetPSTATE_SVCR (svcr : (BitVec 32)) : SailM Unit := do
  (SetPSTATE_SM (BitVec.join1 [(BitVec.access svcr 0)]))
  (SetPSTATE_ZA (BitVec.join1 [(BitVec.access svcr 1)]))

/-- Type quantifiers: esize : Int, slice_name : Int, tile : Int, k_vertical : Bool, width : Nat, width ≥ 0 -/
def ZAslice_read (tile : Int) (esize : Int) (vertical : Bool) (slice_name : Int) (width : Nat) : SailM (BitVec width) := do
  let result ← (( do (undefined_bitvector width) ) : SailM (BitVec width) )
  if (vertical : Bool)
  then
    (do
      sail_assert (width ≥b 0) "src/v8_base.sail:31219.38-31219.39"
      sail_assert (esize ≥b 0) "src/v8_base.sail:31220.38-31220.39"
      sail_assert (((slice_name *i esize) ≤b (((slice_name *i esize) +i esize) -i 1)) || (! ((slice_name ≥b 0) && (((slice_name +i 1) *i esize) ≤b width)))) "src/v8_base.sail:31221.151-31221.152"
      (ZAvslice_read tile esize slice_name width))
  else (do (ZAhslice_read tile esize slice_name width))

/-- Type quantifiers: esize : Int, slice_name : Int, tile : Int, k_vertical : Bool, width : Nat, width ≥ 0 -/
def ZAslice_set (tile : Int) (esize : Int) (vertical : Bool) (slice_name : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  if (vertical : Bool)
  then
    (do
      sail_assert (width ≥b 0) "src/v8_base.sail:31235.38-31235.39"
      sail_assert (esize ≥b 0) "src/v8_base.sail:31236.38-31236.39"
      (ZAvslice_set tile esize slice_name width value_name))
  else (ZAhslice_set tile esize slice_name width value_name)

/-- Type quantifiers: ec : Int -/
def AArch64_SystemAccessTrap (target_el : (BitVec 2)) (ec : Int) : SailM Unit := do
  sail_assert (←((pure ((HaveEL target_el) && (target_el != EL0))) <&&> (do
    (pure ((BitVec.toNat target_el) ≥b (BitVec.toNat (← readReg PSTATE).EL)))))) "src/v8_base.sail:33913.86-33913.87"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (AArch64_SystemAccessTrapSyndrome (← (ThisInstr ())) ec) ) : SailM ExceptionRecord )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)

/-- Type quantifiers: ec : Int -/
def AArch64_AArch32SystemAccessTrap (target_el : (BitVec 2)) (ec : Int) : SailM Unit := do
  sail_assert (←((pure ((HaveEL target_el) && (target_el != EL0))) <&&> (do
    (pure ((BitVec.toNat target_el) ≥b (BitVec.toNat (← readReg PSTATE).EL)))))) "src/v8_base.sail:34008.86-34008.87"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (AArch64_AArch32SystemAccessTrapSyndrome (← (ThisInstr ())) ec) ) : SailM ExceptionRecord )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)

def AArch64_CheckFPAdvSIMDTrap (_ : Unit) : SailM Unit := do
  if ((←((pure (HaveEL EL3)) <&&> (do
       (pure ((_get_CPTR_EL3_Type_TFP (← readReg CPTR_EL3)) == 1#1))) <&&> (do
       (EL3SDDUndefPriority ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
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
          let disabled ← (( do (undefined_bool ()) ) : SailM Bool )
          let disabled ← (( do
            let b__0 ← do (pure (_get_CPTR_EL2_Type_FPEN (← readReg CPTR_EL2)))
            if (((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1))) : Bool)
            then (pure true)
            else
              (do
                if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
                then (do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))
                else (pure false)) ) : SailM Bool )
          let disabled := disabled
          if (disabled : Bool)
          then (AArch64_AdvSIMDFPAccessTrap EL2)
          else (pure ()))
      else
        (do
          if (((_get_CPTR_EL2_Type_TFP (← readReg CPTR_EL2)) == 1#1) : Bool)
          then (AArch64_AdvSIMDFPAccessTrap EL2)
          else (pure ())))
  else (pure ())
  if ((HaveEL EL3) : Bool)
  then
    (do
      if (((_get_CPTR_EL3_Type_TFP (← readReg CPTR_EL3)) == 1#1) : Bool)
      then
        (do
          if ((← (EL3SDDUndef ())) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (AArch64_AdvSIMDFPAccessTrap EL3))
      else (pure ()))
  else (pure ())

def SPEGetRandomInterval (_ : Unit) : SailM (BitVec 8) := do
  let new_byte ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
  if ((! (← readReg __SPE_LFSR_initialized)) : Bool)
  then
    (do
      writeReg __SPE_LFSR_initialized true
      writeReg __SPE_LFSR (Sail.BitVec.extractLsb (← (PC_read__1 ())) 23 0)
      let new_byte ← (( do
        let loop_i_lower := 0
        let loop_i_upper := 7
        let mut loop_vars := new_byte
        for i in [loop_i_upper:loop_i_lower:-1]i do
          let new_byte := loop_vars
          loop_vars ← do
            let new_byte ← (pure (((Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 16 9) ^^^ (Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 21 14)) ^^^ (Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 22 15)))
            let new_byte ← (pure (new_byte ^^^ (Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 23 16)))
            writeReg __SPE_LFSR ((Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 15 0) +++ new_byte)
            (pure new_byte)
        (pure loop_vars) ) : SailM (BitVec 8) )
      (pure ()))
  else
    (do
      let new_byte ← (( do (pure (((Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 16 9) ^^^ (Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 21 14)) ^^^ (Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 22 15))) ) : SailM (BitVec 8) )
      let new_byte ← (( do (pure (new_byte ^^^ (Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 23 16))) ) : SailM (BitVec 8) )
      writeReg __SPE_LFSR ((Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 15 0) +++ new_byte))
  (pure (Sail.BitVec.extractLsb (← readReg __SPE_LFSR) 23 16))

def SPEConstructRecord (_ : Unit) : SailM Unit := do
  let payload_size ← (( do (undefined_int ()) ) : SailM Int )
  (SPEEmptyRecord ())
  if ((← readReg SPESampleContextEL1Valid) : Bool)
  then (SPEAddPacketToRecord 0b01#2 0b0100#4 (← readReg SPESampleContextEL1))
  else (pure ())
  if ((← readReg SPESampleContextEL2Valid) : Bool)
  then (SPEAddPacketToRecord 0b01#2 0b0101#4 (← readReg SPESampleContextEL2))
  else (pure ())
  let loop_counter_index_lower := 0
  let loop_counter_index_upper := (SPEMaxCounters -i 1)
  let mut loop_vars := ()
  for counter_index in [loop_counter_index_lower:loop_counter_index_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((GetElem?.getElem! (← readReg SPESampleCounterValid) counter_index) : Bool)
      then
        (do
          if ((counter_index ≥b 8) : Bool)
          then (SPEAddByteToRecord (0b001000#6 +++ (integer_subrange counter_index 4 3)))
          else (pure ())
          let large_counters ← (( do (__IMPDEF_boolean "SPE 16bit counters") ) : SailM Bool )
          if ((((GetElem?.getElem! (← readReg SPESampleCounter) counter_index) >b (BitVec.toNat 0xFFFF#16)) && large_counters) : Bool)
          then writeReg SPESampleCounter (vectorUpdate (← readReg SPESampleCounter) counter_index (BitVec.toNat 0xFFFF#16))
          else
            (do
              if (((GetElem?.getElem! (← readReg SPESampleCounter) counter_index) >b (BitVec.toNat 0xFFF#12)) : Bool)
              then writeReg SPESampleCounter (vectorUpdate (← readReg SPESampleCounter) counter_index (BitVec.toNat 0xFFF#12))
              else (pure ()))
          (SPEAddPacketToRecord 0b10#2 (1#1 +++ (integer_subrange counter_index 2 0)) (integer_subrange (GetElem?.getElem! (← readReg SPESampleCounter) counter_index) 15 0)))
      else (pure ())
  (pure loop_vars)
  if ((← (HaveStatisticalProfilingv1p2 ())) : Bool)
  then
    (do
      let include_prev_br_name ← (( do (__IMPDEF_boolean "SPE get prev br if not br") ) : SailM Bool )
      if (((bne (← readReg SPESampleOpType) OpType_Branch) && (! include_prev_br_name)) : Bool)
      then writeReg SPESampleAddressValid (vectorUpdate (← readReg SPESampleAddressValid) SPEAddrPosPrevBranchTarget false)
      else (pure ()))
  else (pure ())
  if ((←((pure (! (← (StatisticalProfilingEnabled__1 EL2)))) <&&> (do
       readReg SPESampleInstIsNV2))) : Bool)
  then writeReg SPESampleAddressValid (vectorUpdate (← readReg SPESampleAddressValid) SPEAddrPosDataVirtual false)
  else (pure ())
  let loop_address_index_lower := 0
  let loop_address_index_upper := (SPEMaxAddrs -i 1)
  let mut loop_vars_1 := ()
  for address_index in [loop_address_index_lower:loop_address_index_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      if ((GetElem?.getElem! (← readReg SPESampleAddressValid) address_index) : Bool)
      then
        (do
          if ((address_index ≥b 8) : Bool)
          then (SPEAddByteToRecord (0b001000#6 +++ (integer_subrange address_index 4 3)))
          else (pure ())
          (SPEAddPacketToRecord 0b10#2 (0#1 +++ (integer_subrange address_index 2 0)) (GetElem?.getElem! (← readReg SPESampleAddress) address_index)))
      else (pure ())
  (pure loop_vars_1)
  let payload_size ← (( do
    if ((← readReg SPESampleDataSourceValid) : Bool)
    then
      (do
        let payload_size ← (SPEGetDataSourcePayloadSize ())
        let payload_size := payload_size
        sail_assert ((0 ≤b ((8 *i payload_size) -i 1)) && (((8 *i payload_size) -i 1) <b 16)) "src/v8_base.sail:35364.84-35364.85"
        (SPEAddPacketToRecord 0b01#2 0b0011#4 (Sail.BitVec.extractLsb (← readReg SPESampleDataSource) ((8 *i payload_size) -i 1) 0))
        (pure payload_size))
    else (pure payload_size) ) : SailM Int )
  (SPEAddPacketToRecord 0b01#2 (0b10#2 +++ (← readReg SPESampleClass)) (← readReg SPESampleSubclass))
  let payload_size ← do (SPEGetEventsPayloadSize ())
  sail_assert ((0 ≤b ((8 *i payload_size) -i 1)) && (((8 *i payload_size) -i 1) <b 64)) "src/v8_base.sail:35369.80-35369.81"
  sail_assert ((((((8 *i payload_size) -i 1) -i 0) +i 1) == 8) || ((((((8 *i payload_size) -i 1) -i 0) +i 1) == 16) || ((((((8 *i payload_size) -i 1) -i 0) +i 1) == 32) || (((((8 *i payload_size) -i 1) -i 0) +i 1) == 64)))) "src/v8_base.sail:35370.173-35370.174"
  (SPEAddPacketToRecord 0b01#2 0b0010#4 (Sail.BitVec.extractLsb (← readReg SPESampleEvents) ((8 *i payload_size) -i 1) 0))
  if ((← readReg SPESampleTimestampValid) : Bool)
  then (SPEAddPacketToRecord 0b01#2 0b0001#4 (← readReg SPESampleTimestamp))
  else (SPEAddByteToRecord 0b00000001#8)
  let mut loop_vars_2 := ()
  while (← (λ _ => do (pure ((fmod_int (← readReg SPERecordSize) (Int.shiftl 1 (BitVec.toNat (_get_PMBIDR_EL1_Type_Align (← readReg PMBIDR_EL1))))) != 0))) loop_vars_2) do
    let () := loop_vars_2
    loop_vars_2 ← do (SPEAddByteToRecord (Zeros (n := 8)))
  (pure loop_vars_2)
  (SPEWriteToBuffer ())

def AArch64_IC (opscope : CacheOpScope) : SailM Unit := do
  let regval ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  (AArch64_IC__1 regval opscope)

/-- Type quantifiers: k_is_ATS1Ex : Bool -/
def AArch64_EncodePAR (regime : Regime) (is_ATS1Ex : Bool) (addrdesc : AddressDescriptor) : SailM Unit := do
  (PAR_EL1_write (Mk_PAR_EL1_Type (Zeros (n := 128))))
  let paspace : PASpace := addrdesc.paddress.paspace
  if ((← (AArch64_isPARFormatD128 regime is_ATS1Ex)) : Bool)
  then (PAR_EL1_write (_update_PAR_EL1_Type_D128 (← (PAR_EL1_read ())) 1#1))
  else (PAR_EL1_write (_update_PAR_EL1_Type_D128 (← (PAR_EL1_read ())) 0#1))
  if ((! (IsFault addrdesc)) : Bool)
  then
    (do
      (PAR_EL1_write (_update_PAR_EL1_Type_F (← (PAR_EL1_read ())) 0#1))
      if ((← (HaveRME ())) : Bool)
      then
        (do
          if ((BEq.beq regime Regime_EL3) : Bool)
          then
            (do
              match paspace with
              | .PAS_Secure =>
                (do
                  let __tmp ← (( do (PAR_EL1_read ()) ) : SailM PAR_EL1_Type )
                  let __tmp : (BitVec 128) :=
                    let __tmp : (BitVec 128) := (Sail.BitVec.updateSubrange __tmp 11 11 (Sail.BitVec.extractLsb 0b00#2 1 1))
                    (Sail.BitVec.updateSubrange __tmp 9 9 (Sail.BitVec.extractLsb 0b00#2 0 0))
                  (PAR_EL1_write __tmp))
              | .PAS_NonSecure =>
                (do
                  let __tmp ← (( do (PAR_EL1_read ()) ) : SailM PAR_EL1_Type )
                  let __tmp : (BitVec 128) :=
                    let __tmp : (BitVec 128) := (Sail.BitVec.updateSubrange __tmp 11 11 (Sail.BitVec.extractLsb 0b01#2 1 1))
                    (Sail.BitVec.updateSubrange __tmp 9 9 (Sail.BitVec.extractLsb 0b01#2 0 0))
                  (PAR_EL1_write __tmp))
              | .PAS_Root =>
                (do
                  let __tmp ← (( do (PAR_EL1_read ()) ) : SailM PAR_EL1_Type )
                  let __tmp : (BitVec 128) :=
                    let __tmp : (BitVec 128) := (Sail.BitVec.updateSubrange __tmp 11 11 (Sail.BitVec.extractLsb 0b10#2 1 1))
                    (Sail.BitVec.updateSubrange __tmp 9 9 (Sail.BitVec.extractLsb 0b10#2 0 0))
                  (PAR_EL1_write __tmp))
              | .PAS_Realm =>
                (do
                  let __tmp ← (( do (PAR_EL1_read ()) ) : SailM PAR_EL1_Type )
                  let __tmp : (BitVec 128) :=
                    let __tmp : (BitVec 128) := (Sail.BitVec.updateSubrange __tmp 11 11 (Sail.BitVec.extractLsb 0b11#2 1 1))
                    (Sail.BitVec.updateSubrange __tmp 9 9 (Sail.BitVec.extractLsb 0b11#2 0 0))
                  (PAR_EL1_write __tmp)))
          else
            (do
              if ((BEq.beq (← (SecurityStateForRegime regime)) SS_Secure) : Bool)
              then
                (do
                  (PAR_EL1_write (_update_PAR_EL1_Type_NSE (← (PAR_EL1_read ())) (← (__UNKNOWN_bit ()))))
                  (PAR_EL1_write
                    (_update_PAR_EL1_Type_NS (← (PAR_EL1_read ()))
                      (if ((BEq.beq paspace PAS_Secure) : Bool)
                      then 0#1
                      else 1#1))))
              else
                (do
                  if ((BEq.beq (← (SecurityStateForRegime regime)) SS_Realm) : Bool)
                  then
                    (do
                      if (((BEq.beq regime Regime_EL10) && is_ATS1Ex) : Bool)
                      then
                        (do
                          (PAR_EL1_write (_update_PAR_EL1_Type_NSE (← (PAR_EL1_read ())) (← (__UNKNOWN_bit ()))))
                          (PAR_EL1_write (_update_PAR_EL1_Type_NS (← (PAR_EL1_read ())) (← (__UNKNOWN_bit ())))))
                      else
                        (do
                          (PAR_EL1_write (_update_PAR_EL1_Type_NSE (← (PAR_EL1_read ())) (← (__UNKNOWN_bit ()))))
                          (PAR_EL1_write
                            (_update_PAR_EL1_Type_NS (← (PAR_EL1_read ()))
                              (if ((BEq.beq paspace PAS_Realm) : Bool)
                              then 0#1
                              else 1#1)))))
                  else
                    (do
                      (PAR_EL1_write (_update_PAR_EL1_Type_NSE (← (PAR_EL1_read ())) (← (__UNKNOWN_bit ()))))
                      (PAR_EL1_write (_update_PAR_EL1_Type_NS (← (PAR_EL1_read ())) (← (__UNKNOWN_bit ()))))))))
      else
        (do
          (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 11 11 1#1)))
          if ((BEq.beq (← (SecurityStateForRegime regime)) SS_Secure) : Bool)
          then
            (PAR_EL1_write
              (_update_PAR_EL1_Type_NS (← (PAR_EL1_read ()))
                (if ((BEq.beq paspace PAS_Secure) : Bool)
                then 0#1
                else 1#1)))
          else (PAR_EL1_write (_update_PAR_EL1_Type_NS (← (PAR_EL1_read ())) (← (__UNKNOWN_bit ())))))
      (PAR_EL1_write (_update_PAR_EL1_Type_SH (← (PAR_EL1_read ())) (← (ReportedPARShareability (PAREncodeShareability addrdesc.memattrs)))))
      if (((_get_PAR_EL1_Type_D128 (← (PAR_EL1_read ()))) == 1#1) : Bool)
      then (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 119 76 (Sail.BitVec.extractLsb addrdesc.paddress.address 55 12))))
      else (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 55 12 (Sail.BitVec.extractLsb addrdesc.paddress.address 55 12))))
      (PAR_EL1_write (_update_PAR_EL1_Type_ATTR (← (PAR_EL1_read ())) (← (ReportedPARAttrs (← (EncodePARAttrs addrdesc.memattrs))))))
      (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 10 10 (← (__IMPDEF_bit "Non-Faulting PAR"))))))
  else
    (do
      (PAR_EL1_write (_update_PAR_EL1_Type_F (← (PAR_EL1_read ())) 1#1))
      (PAR_EL1_write
        (_update_PAR_EL1_Type_DirtyBit (← (PAR_EL1_read ()))
          (if (addrdesc.fault.dirtybit : Bool)
          then 1#1
          else 0#1)))
      (PAR_EL1_write
        (_update_PAR_EL1_Type_Overlay (← (PAR_EL1_read ()))
          (if (addrdesc.fault.overlay : Bool)
          then 1#1
          else 0#1)))
      (PAR_EL1_write
        (_update_PAR_EL1_Type_TopLevel (← (PAR_EL1_read ()))
          (if (addrdesc.fault.toplevel : Bool)
          then 1#1
          else 0#1)))
      (PAR_EL1_write
        (_update_PAR_EL1_Type_AssuredOnly (← (PAR_EL1_read ()))
          (if (addrdesc.fault.assuredonly : Bool)
          then 1#1
          else 0#1)))
      (PAR_EL1_write (_update_PAR_EL1_Type_FST (← (PAR_EL1_read ())) (← (AArch64_PARFaultStatus addrdesc.fault))))
      (PAR_EL1_write
        (_update_PAR_EL1_Type_PTW (← (PAR_EL1_read ()))
          (if (addrdesc.fault.s2fs1walk : Bool)
          then 1#1
          else 0#1)))
      (PAR_EL1_write
        (_update_PAR_EL1_Type_S (← (PAR_EL1_read ()))
          (if (addrdesc.fault.secondstage : Bool)
          then 1#1
          else 0#1)))
      (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 11 11 1#1)))
      (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange (← (PAR_EL1_read ())) 63 48 (← (__IMPDEF_bits 16 "Faulting PAR"))))))

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV84 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap4_IMPLEMENTED enabled
  if (enabled : Bool)
  then (__ConfigureV83 enabled)
  else (pure ())

def AArch32_IC (opscope : CacheOpScope) : SailM Unit := do
  let regval ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (AArch32_IC__1 regval opscope)

def AArch32_AT (vaddress : (BitVec 32)) (stage_in : TranslationStage) (el : (BitVec 2)) (ataccess : ATAccess) : SailM Unit := do
  let stage : TranslationStage := stage_in
  let ss ← (( do (undefined_SecurityState ()) ) : SailM SecurityState )
  let regime ← (( do (undefined_Regime ()) ) : SailM Regime )
  let eae ← (( do (undefined_bool ()) ) : SailM Bool )
  let (eae, regime, ss, stage) ← (( do
    if ((el == EL2) : Bool)
    then
      (let regime : Regime := Regime_EL2
      let eae : Bool := true
      let ss : SecurityState := SS_NonSecure
      (pure (eae, regime, ss, stage)))
    else
      (do
        let (eae, regime, ss, stage) ← (( do
          if (((BEq.beq stage TranslationStage_1) || ((BEq.beq stage TranslationStage_12) && (! (HaveEL EL2)))) : Bool)
          then
            (do
              let stage : TranslationStage := TranslationStage_1
              let ss ← (SecurityStateAtEL (← readReg PSTATE).EL)
              let regime ←
                if ((←((pure (BEq.beq ss SS_Secure)) <&&> (do
                     (ELUsingAArch32 EL3)))) : Bool)
                then (pure Regime_EL30)
                else (pure Regime_EL10)
              let eae ← (pure ((_get_TTBCR_Type_EAE (← (TTBCR_read ()))) == 1#1))
              (pure (eae, regime, ss, stage)))
          else
            (do
              let regime : Regime := Regime_EL10
              let eae ←
                if ((HaveAArch32EL EL3) : Bool)
                then (pure ((_get_TTBCR_Type_EAE (← (TTBCR_NS_read ()))) == 1#1))
                else (pure ((_get_TTBCR_Type_EAE (← (TTBCR_read ()))) == 1#1))
              let ss : SecurityState := SS_NonSecure
              (pure (eae, regime, ss, stage))) ) : SailM (Bool × Regime × SecurityState × TranslationStage) )
        (pure (eae, regime, ss, stage))) ) : SailM (Bool × Regime × SecurityState × TranslationStage) )
  let addrdesc ← (( do (undefined_AddressDescriptor ()) ) : SailM AddressDescriptor )
  let sdftype ← (( do (undefined_SDFType ()) ) : SailM SDFType )
  let aligned : Bool := true
  let supersection : (BitVec 1) := 0#1
  let write : Bool := ((BEq.beq ataccess ATAccess_WritePAN) || (BEq.beq ataccess ATAccess_Write))
  let pan : Bool := ((BEq.beq ataccess ATAccess_WritePAN) || (BEq.beq ataccess ATAccess_ReadPAN))
  let accdesc ← (( do (CreateAccDescAT ss el write pan) ) : SailM AccessDescriptor )
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let tsi ← do (AArch32_GetTranslationStartInfo regime ss accdesc vaddress 1)
  (start_translation tsi)
  let (addrdesc, fault, supersection) ← (( do
    if (eae : Bool)
    then
      (do
        let (tup__0, tup__1) ← do (AArch32_S1TranslateLD fault regime vaddress aligned accdesc)
        let fault : FaultRecord := tup__0
        let addrdesc : AddressDescriptor := tup__1
        (pure (addrdesc, fault, supersection)))
    else
      (do
        let (addrdesc, fault, sdftype) ← (( do
          let (tup__0, tup__1, tup__2) ← do (AArch32_S1TranslateSD fault regime vaddress aligned accdesc)
          let fault : FaultRecord := tup__0
          let addrdesc : AddressDescriptor := tup__1
          let sdftype : SDFType := tup__2
          (pure (addrdesc, fault, sdftype)) ) : SailM (AddressDescriptor × FaultRecord × SDFType) )
        let supersection : (BitVec 1) :=
          if ((BEq.beq sdftype SDFType_Supersection) : Bool)
          then 1#1
          else 0#1
        (pure (addrdesc, fault, supersection))) ) : SailM (AddressDescriptor × FaultRecord × (BitVec 1)) )
  let (addrdesc, fault) ← (( do
    if (((BEq.beq stage TranslationStage_12) && (BEq.beq fault.statuscode Fault_None)) : Bool)
    then
      (do
        let (tup__0, tup__1) ← do (AArch32_S2Translate fault addrdesc none aligned accdesc)
        let fault : FaultRecord := tup__0
        let addrdesc : AddressDescriptor := tup__1
        (pure (addrdesc, fault)))
    else (pure (addrdesc, fault)) ) : SailM (AddressDescriptor × FaultRecord) )
  if ((bne fault.statuscode Fault_None) : Bool)
  then
    (do
      if ((←((IsExternalAbort__1 fault) <||> (do
           (pure ((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do (EL2Enabled ())))) && fault.s2fs1walk))))) : Bool)
      then
        (do
          (PAR_write (Mk_PAR_Type (← (__UNKNOWN_bits 64))))
          (AArch32_Abort vaddress fault))
      else (pure ()))
  else (pure ())
  let addrdesc : AddressDescriptor := { addrdesc with fault := fault }
  (end_translation addrdesc)
  if ((←((pure eae) <||> (do
       (pure (BEq.beq stage TranslationStage_12)) <&&> (do
         (pure ((_get_HCR_Type_VM (← (HCR_read ()))) == 1#1)) <||> (do
           (pure ((_get_HCR_Type_DC (← (HCR_read ()))) == 1#1))))) <||> (do
       (pure ((BEq.beq stage TranslationStage_1) && (el != EL2))) <&&> (do
         (pure ((← readReg PSTATE).EL == EL2)))))) : Bool)
  then (AArch32_EncodePARLD addrdesc ss)
  else (AArch32_EncodePARSD addrdesc supersection ss)

def A32ExpandImm (imm12 : (BitVec 12)) : SailM (BitVec 32) := do
  let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (__tup_0, _) ← do (A32ExpandImm_C imm12 (← readReg PSTATE).C)
  (pure __tup_0)

/-- Type quantifiers: ec : Int -/
def AArch32_TakeHypTrapException (ec : Int) : SailM Unit := do
  let except ← (( do (AArch32_SystemAccessTrapSyndrome (← (ThisInstr ())) ec) ) : SailM ExceptionRecord )
  (AArch32_TakeHypTrapException__1 except)

/-- Type quantifiers: ec : Int -/
def AArch32_SystemAccessTrap (mode : (BitVec 5)) (ec : Int) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  let target_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let valid_name ← (( do (undefined_bool ()) ) : SailM Bool )
  let (target_el, valid_name) ← (( do
    let (tup__0, tup__1) ← do (ELFromM32 mode)
    let valid_name : Bool := tup__0
    let target_el : (BitVec 2) := tup__1
    (pure (target_el, valid_name)) ) : SailM ((BitVec 2) × Bool) )
  sail_assert (←((pure ((valid_name && (HaveEL target_el)) && (target_el != EL0))) <&&> (do
    (pure ((BitVec.toNat target_el) ≥b (BitVec.toNat (← readReg PSTATE).EL)))))) "src/v8_base.sail:41526.101-41526.102"
  if ((target_el == EL2) : Bool)
  then
    (do
      let except ← (( do (AArch32_SystemAccessTrapSyndrome (← (ThisInstr ())) ec) ) : SailM ExceptionRecord )
      (AArch32_TakeHypTrapException__1 except))
  else (AArch32_TakeUndefInstrException ())

/-- Type quantifiers: size : Nat, (size * 8) ≥ 0 -/
def Mem_with_type_set (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) (value_in_name : (BitVec (size * 8))) : SailM Unit := do
  let ispair : Bool := false
  (Mem_with_type_set__1 address size accdesc ispair value_in_name)

/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemA_read (address : (BitVec 32)) (size : Nat) : SailM (BitVec (8 * size)) := do
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_LOAD acqrel tagchecked) ) : SailM AccessDescriptor )
  (Mem_with_type_read address size accdesc)

/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemU_read (address : (BitVec 32)) (size : Nat) : SailM (BitVec (8 * size)) := do
  let nontemporal : Bool := false
  let privileged ← (( do (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescGPR MemOp_LOAD nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  (Mem_with_type_read address size accdesc)

/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemU_unpriv_read (address : (BitVec 32)) (size : Nat) : SailM (BitVec (8 * size)) := do
  let nontemporal : Bool := false
  let privileged : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescGPR MemOp_LOAD nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  (Mem_with_type_read address size accdesc)

/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemO_read (address : (BitVec 32)) (size : Nat) : SailM (BitVec (8 * size)) := do
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescAcqRel MemOp_LOAD tagchecked) ) : SailM AccessDescriptor )
  (Mem_with_type_read address size accdesc)

/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemS_read (address : (BitVec 32)) (size : Nat) : SailM (BitVec (8 * size)) := do
  let accdesc ← (( do (CreateAccDescA32LSMD MemOp_LOAD) ) : SailM AccessDescriptor )
  (Mem_with_type_read address size accdesc)

def PCStoreValue (_ : Unit) : SailM (BitVec 32) := do
  (PC_read__1 ())

def AArch32_ESBOperation (_ : Unit) : SailM Unit := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let route_to_aarch64 ← (( do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (pure (! (← (ELUsingAArch32 EL1))))) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if ((←((pure (! route_to_aarch64)) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure (! (← (ELUsingAArch32 EL2))))))) : Bool)
    then (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do (pure ((_get_HCR_EL2_Type_AMO (← readReg HCR_EL2)) == 1#1))))
    else (pure route_to_aarch64) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if ((←((pure ((! route_to_aarch64) && (HaveEL EL3))) <&&> (do
         (pure (! (← (ELUsingAArch32 EL3))))))) : Bool)
    then (do (pure ((← (EffectiveEA ())) == 1#1)))
    else (pure route_to_aarch64) ) : SailM Bool )
  if (route_to_aarch64 : Bool)
  then (do (AArch64_ESBOperation ()))
  else
    (do
      let route_to_monitor ← (( do (pure (HaveEL EL3)) <&&> (do (ELUsingAArch32 EL3)) <&&> (do (pure ((← (EffectiveEA ())) == 1#1))) ) : SailM Bool )
      let route_to_hyp ← (( do (pure ((← readReg PSTATE).EL == EL0)) <||> (do (pure ((← readReg PSTATE).EL == EL1))) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1)) <||> (do (pure ((_get_HCR_Type_AMO (← (HCR_read ()))) == 1#1)))) ) : SailM Bool )
      let target ← (( do (undefined_bitvector 5) ) : SailM (BitVec 5) )
      let target ← (( do
        if (route_to_monitor : Bool)
        then (pure M32_Monitor)
        else
          (do
            if ((←((pure route_to_hyp) <||> (do
                 (pure ((← readReg PSTATE).M == M32_Hyp))))) : Bool)
            then (pure M32_Hyp)
            else (pure M32_Abort)) ) : SailM (BitVec 5) )
      let mask_active ← (( do (undefined_bool ()) ) : SailM Bool )
      let mask_active ← (( do
        if ((BEq.beq (← (CurrentSecurityState ())) SS_Secure) : Bool)
        then (pure true)
        else
          (do
            if ((target == M32_Monitor) : Bool)
            then (do (pure ((_get_SCR_Type_AW (← readReg SCR)) == 1#1)) <&&> (do (pure (! (HaveEL EL2))) <||> (do (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 0#1)) <&&> (do (pure ((_get_HCR_Type_AMO (← (HCR_read ()))) == 0#1))))))
            else (do (pure (target == M32_Abort)) <||> (do (pure ((← readReg PSTATE).M == M32_Hyp))))) ) : SailM Bool )
      let mask_set ← (( do (pure ((← readReg PSTATE).A == 1#1)) ) : SailM Bool )
      let el ← (( do
        let (_, __tup_1) ← do (ELFromM32 target)
        (pure __tup_1) ) : SailM (BitVec 2) )
      let intdis ← (( do (Halted ()) <||> (do (ExternalDebugInterruptsDisabled el)) ) : SailM Bool )
      let masked : Bool := (intdis || (mask_active && mask_set))
      if ((←((pure masked) <&&> (do
           (IsSynchronizablePhysicalSErrorPending ())))) : Bool)
      then
        (do
          let syndrome : (BitVec 32) := (Zeros (n := 32))
          let syndrome : (BitVec 32) := (BitVec.update syndrome 31 (Bit 1#1))
          let syndrome ← (pure (Sail.BitVec.updateSubrange syndrome 15 0 (← (AArch32_PhysicalSErrorSyndrome ()))))
          (DISR_write (Mk_DISR_Type syndrome))
          (pure (ClearPendingPhysicalSError ())))
      else (pure ()))

def MAIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR0_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (MAIR0_S_write r)
  else (MAIR0_NS_write r)

def MAIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR1_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then (MAIR1_S_write r)
  else (MAIR1_NS_write r)

/-- Type quantifiers: k_N : Nat, 31 < k_N -/
def SetPSTATEFromPSR (spsr : (BitVec k_N)) : SailM Unit := do
  let illegal_psr_state ← (( do (IllegalExceptionReturn spsr) ) : SailM Bool )
  (SetPSTATEFromPSR__1 spsr illegal_psr_state)

/-- Type quantifiers: localtimeout : Int -/
def Hint_WFE (localtimeout : Int) (wfxtype : WFxType) : SailM Unit := do
  let delay ← (( do (undefined_int ()) ) : SailM Int )
  let delay_enabled ← (( do (undefined_bool ()) ) : SailM Bool )
  let sctlr ← (( do (undefined_SCTLRType ()) ) : SailM SCTLRType )
  let trap ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((← (IsEventRegisterSet ())) : Bool)
  then (ClearEventRegister ())
  else
    (do
      if ((←((HaveFeatWFxT ()) <&&> (do
           (LocalTimeoutEvent localtimeout)))) : Bool)
      then (EndOfInstruction ())
      else
        (do
          let target_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
          let trap : Bool := false
          let (target_el, trap) ← (( do
            if (((← readReg PSTATE).EL == EL0) : Bool)
            then
              (do
                let (target_el, trap) ← (( do
                  if ((← (HaveTWEDExt ())) : Bool)
                  then
                    (do
                      let sctlr ← (( do (SCTLR_read__1 ()) ) : SailM SCTLRType )
                      let trap : Bool := ((_get_SCTLRType_nTWE sctlr) == 0#1)
                      let target_el : (BitVec 2) := EL1
                      (pure (target_el, trap)))
                  else
                    (do
                      (AArch64_CheckForWFxTrap EL1 wfxtype)
                      (pure (target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
                (pure (target_el, trap)))
            else (pure (target_el, trap)) ) : SailM ((BitVec 2) × Bool) )
          let (target_el, trap) ← (( do
            if ((←((pure (! trap)) <&&> (do
                 (pure ((← readReg PSTATE).EL == EL0)) <||> (do
                   (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
                 (EL2Enabled ())) <&&> (do
                 (pure (! (← (IsInHost ()))))))) : Bool)
            then
              (do
                let (target_el, trap) ← (( do
                  if ((← (HaveTWEDExt ())) : Bool)
                  then
                    (do
                      let trap ← (pure ((_get_HCR_EL2_Type_TWE (← readReg HCR_EL2)) == 1#1))
                      let target_el : (BitVec 2) := EL2
                      (pure (target_el, trap)))
                  else
                    (do
                      (AArch64_CheckForWFxTrap EL2 wfxtype)
                      (pure (target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
                (pure (target_el, trap)))
            else (pure (target_el, trap)) ) : SailM ((BitVec 2) × Bool) )
          let (target_el, trap) ← (( do
            if ((←((pure ((! trap) && (HaveEL EL3))) <&&> (do
                 (pure ((← readReg PSTATE).EL != EL3))))) : Bool)
            then
              (do
                let (target_el, trap) ← (( do
                  if ((← (HaveTWEDExt ())) : Bool)
                  then
                    (do
                      let trap ← (pure ((_get_SCR_EL3_Type_TWE (← readReg SCR_EL3)) == 1#1))
                      let target_el : (BitVec 2) := EL3
                      (pure (target_el, trap)))
                  else
                    (do
                      (AArch64_CheckForWFxTrap EL3 wfxtype)
                      (pure (target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
                (pure (target_el, trap)))
            else (pure (target_el, trap)) ) : SailM ((BitVec 2) × Bool) )
          if ((←((pure trap) <&&> (do
               (pure ((← readReg PSTATE).EL != EL3))))) : Bool)
          then
            (do
              let (delay, delay_enabled) ← (( do
                let (tup__0, tup__1) ← do (WFETrapDelay target_el)
                let delay_enabled : Bool := tup__0
                let delay : Int := tup__1
                (pure (delay, delay_enabled)) ) : SailM (Int × Bool) )
              let delay := delay
              if ((! (← (WaitForEventUntilDelay delay_enabled delay))) : Bool)
              then (AArch64_WFxTrap wfxtype target_el)
              else (pure ()))
          else (WaitForEvent localtimeout)))

/-- Type quantifiers: localtimeout : Int -/
def Hint_WFI (localtimeout : Int) (wfxtype : WFxType) : SailM Unit := do
  if ((←((HaveTME ()) <&&> (do
       (pure ((← readReg TSTATE).depth >b 0))))) : Bool)
  then (FailTransaction TMFailure_ERR false)
  else (pure ())
  if ((←((InterruptPending ()) <||> (do
       (HaveFeatWFxT ()) <&&> (do
         (LocalTimeoutEvent localtimeout))))) : Bool)
  then (EndOfInstruction ())
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then (AArch64_CheckForWFxTrap EL1 wfxtype)
      else (pure ())
      if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
           (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
           (EL2Enabled ())) <&&> (do
           (pure (! (← (IsInHost ()))))))) : Bool)
      then (AArch64_CheckForWFxTrap EL2 wfxtype)
      else (pure ())
      if ((←((pure (HaveEL EL3)) <&&> (do
           (pure ((← readReg PSTATE).EL != EL3))))) : Bool)
      then (AArch64_CheckForWFxTrap EL3 wfxtype)
      else (pure ())
      (WaitForInterrupt localtimeout))

/-- Type quantifiers: N : Nat, k_fpexc : Bool, List.elem N [16, 32, 64] -/
def FPRound__2 (op : real) (fpcr_in : (BitVec 64)) (rounding : FPRounding) (fpexc : Bool) (N : Nat) : SailM (BitVec N) := do
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  let isbfloat16 : Bool := false
  (FPRoundBase__1 op fpcr rounding isbfloat16 fpexc N)

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPUnpackBase (fpval : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (FPType × (BitVec 1) × real) := do
  let fp_type ← (( do (undefined_FPType ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real ()) ) : SailM real )
  let isbfloat16 : Bool := false
  let (fp_type, sign, value_name) ← (( do
    let (tup__0, tup__1, tup__2) ← do (FPUnpackBase__1 fpval fpcr fpexc isbfloat16)
    let fp_type : FPType := tup__0
    let sign : (BitVec 1) := tup__1
    let value_name : real := tup__2
    (pure (fp_type, sign, value_name)) ) : SailM (FPType × (BitVec 1) × real) )
  (pure (fp_type, sign, value_name))

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPProcessNaN (fptype : FPType) (op : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (FPProcessNaN__1 fptype op fpcr fpexc)

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPProcessNaNs__1 (type1 : FPType) (type2 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  sail_assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length op2) == 64))) "src/v8_base.sail:16206.41-16206.42"
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  let any_snan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN))
  let type_nan : FPType :=
    if (any_snan : Bool)
    then FPType_SNaN
    else FPType_QNaN
  let (done, result) ← (( do
    if (((altfp && op1_nan) && op2_nan) : Bool)
    then
      (do
        let done : Bool := true
        let result ← (FPProcessNaN__1 type_nan op1 fpcr fpexc)
        (pure (done, result)))
    else
      (do
        let (done, result) ← (( do
          if ((BEq.beq type1 FPType_SNaN) : Bool)
          then
            (do
              let done : Bool := true
              let result ← (FPProcessNaN__1 type1 op1 fpcr fpexc)
              (pure (done, result)))
          else
            (do
              let (done, result) ← (( do
                if ((BEq.beq type2 FPType_SNaN) : Bool)
                then
                  (do
                    let done : Bool := true
                    let result ← (FPProcessNaN__1 type2 op2 fpcr fpexc)
                    (pure (done, result)))
                else
                  (do
                    let (done, result) ← (( do
                      if ((BEq.beq type1 FPType_QNaN) : Bool)
                      then
                        (do
                          let done : Bool := true
                          let result ← (FPProcessNaN__1 type1 op1 fpcr fpexc)
                          (pure (done, result)))
                      else
                        (do
                          let (done, result) ← (( do
                            if ((BEq.beq type2 FPType_QNaN) : Bool)
                            then
                              (do
                                let done : Bool := true
                                let result ← (FPProcessNaN__1 type2 op2 fpcr fpexc)
                                (pure (done, result)))
                            else
                              (let done : Bool := false
                              let result : (BitVec k_N) := (Zeros (n := (Sail.BitVec.length result)))
                              (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                          (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                    (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
              (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
        (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
  (pure (done, result))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPRoundCV (op : real) (fpcr_in : (BitVec 64)) (rounding : FPRounding) (N : Nat) : SailM (BitVec N) := do
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 19 19 0#1)
  let fpexc : Bool := true
  let isbfloat16 : Bool := false
  (FPRoundBase__1 op fpcr rounding isbfloat16 fpexc N)

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPProcessNaNs3__1 (type1 : FPType) (type2 : FPType) (type3 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (op3 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  sail_assert (((Sail.BitVec.length op3) == 16) || (((Sail.BitVec.length op3) == 32) || ((Sail.BitVec.length op3) == 64))) "src/v8_base.sail:16864.41-16864.42"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op3)) ) : SailM (BitVec k_N) )
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  let op3_nan : Bool := ((BEq.beq type3 FPType_SNaN) || (BEq.beq type3 FPType_QNaN))
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let type_nan ← (( do (undefined_FPType ()) ) : SailM FPType )
  let type_nan : FPType :=
    if (altfp : Bool)
    then
      (if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) || (BEq.beq type3 FPType_SNaN)) : Bool)
      then FPType_SNaN
      else FPType_QNaN)
    else type_nan
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let (done, result) ← (( do
    if ((((altfp && op1_nan) && op2_nan) && op3_nan) : Bool)
    then
      (do
        let done : Bool := true
        let result ← (FPProcessNaN__1 type_nan op2 fpcr fpexc)
        (pure (done, result)))
    else
      (do
        let (done, result) ← (( do
          if (((altfp && op2_nan) && (op1_nan || op3_nan)) : Bool)
          then
            (do
              let done : Bool := true
              let result ← (FPProcessNaN__1 type_nan op2 fpcr fpexc)
              (pure (done, result)))
          else
            (do
              let (done, result) ← (( do
                if (((altfp && op3_nan) && op1_nan) : Bool)
                then
                  (do
                    let done : Bool := true
                    let result ← (FPProcessNaN__1 type_nan op3 fpcr fpexc)
                    (pure (done, result)))
                else
                  (do
                    let (done, result) ← (( do
                      if ((BEq.beq type1 FPType_SNaN) : Bool)
                      then
                        (do
                          let done : Bool := true
                          let result ← (FPProcessNaN__1 type1 op1 fpcr fpexc)
                          (pure (done, result)))
                      else
                        (do
                          let (done, result) ← (( do
                            if ((BEq.beq type2 FPType_SNaN) : Bool)
                            then
                              (do
                                let done : Bool := true
                                let result ← (FPProcessNaN__1 type2 op2 fpcr fpexc)
                                (pure (done, result)))
                            else
                              (do
                                let (done, result) ← (( do
                                  if ((BEq.beq type3 FPType_SNaN) : Bool)
                                  then
                                    (do
                                      let done : Bool := true
                                      let result ← (FPProcessNaN__1 type3 op3 fpcr fpexc)
                                      (pure (done, result)))
                                  else
                                    (do
                                      let (done, result) ← (( do
                                        if ((BEq.beq type1 FPType_QNaN) : Bool)
                                        then
                                          (do
                                            let done : Bool := true
                                            let result ← (FPProcessNaN__1 type1 op1 fpcr fpexc)
                                            (pure (done, result)))
                                        else
                                          (do
                                            let (done, result) ← (( do
                                              if ((BEq.beq type2 FPType_QNaN) : Bool)
                                              then
                                                (do
                                                  let done : Bool := true
                                                  let result ← (FPProcessNaN__1 type2 op2 fpcr fpexc)
                                                  (pure (done, result)))
                                              else
                                                (do
                                                  let (done, result) ← (( do
                                                    if ((BEq.beq type3 FPType_QNaN) : Bool)
                                                    then
                                                      (do
                                                        let done : Bool := true
                                                        let result ← (FPProcessNaN__1 type3 op3 fpcr fpexc)
                                                        (pure (done, result)))
                                                    else
                                                      (let done : Bool := false
                                                      let result : (BitVec k_N) := (Zeros (n := (Sail.BitVec.length result)))
                                                      (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                                  (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                            (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                      (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                          (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                    (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
              (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
        (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
  (pure (done, result))

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [32, 64] -/
def FPProcessNaNs3H (type1 : FPType) (type2 : FPType) (type3 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec (k_N / 2))) (op3 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  sail_assert (((Sail.BitVec.length op1) == 32) || ((Sail.BitVec.length op1) == 64)) "src/v8_base.sail:17069.30-17069.31"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op1)) ) : SailM (BitVec k_N) )
  let type_nan ← (( do (undefined_FPType ()) ) : SailM FPType )
  let altfp ← (( do (pure ((←((HaveAltFP ()) <&&> (do (pure (! (← (UsingAArch32 ()))))))) && ((_get_FPCRType_AH fpcr) == 1#1))) ) : SailM Bool )
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  let op3_nan : Bool := ((BEq.beq type3 FPType_SNaN) || (BEq.beq type3 FPType_QNaN))
  let type_nan : FPType :=
    if (altfp : Bool)
    then
      (if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) || (BEq.beq type3 FPType_SNaN)) : Bool)
      then FPType_SNaN
      else FPType_QNaN)
    else type_nan
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let (done, result) ← (( do
    if ((((altfp && op1_nan) && op2_nan) && op3_nan) : Bool)
    then
      (do
        let done : Bool := true
        let result ← (FPConvertNaN (← (FPProcessNaN__1 type_nan op2 fpcr fpexc)) (Sail.BitVec.length result))
        (pure (done, result)))
    else
      (do
        let (done, result) ← (( do
          if (((altfp && op2_nan) && (op1_nan || op3_nan)) : Bool)
          then
            (do
              let done : Bool := true
              let result ← (FPConvertNaN (← (FPProcessNaN__1 type_nan op2 fpcr fpexc)) (Sail.BitVec.length result))
              (pure (done, result)))
          else
            (do
              let (done, result) ← (( do
                if (((altfp && op3_nan) && op1_nan) : Bool)
                then
                  (do
                    let done : Bool := true
                    let result ← (FPConvertNaN (← (FPProcessNaN__1 type_nan op3 fpcr fpexc)) (Sail.BitVec.length result))
                    (pure (done, result)))
                else
                  (do
                    let (done, result) ← (( do
                      if ((BEq.beq type1 FPType_SNaN) : Bool)
                      then
                        (do
                          let done : Bool := true
                          let result ← (FPProcessNaN__1 type1 op1 fpcr fpexc)
                          (pure (done, result)))
                      else
                        (do
                          let (done, result) ← (( do
                            if ((BEq.beq type2 FPType_SNaN) : Bool)
                            then
                              (do
                                let done : Bool := true
                                let result ← (FPConvertNaN (← (FPProcessNaN__1 type2 op2 fpcr fpexc)) (Sail.BitVec.length result))
                                (pure (done, result)))
                            else
                              (do
                                let (done, result) ← (( do
                                  if ((BEq.beq type3 FPType_SNaN) : Bool)
                                  then
                                    (do
                                      let done : Bool := true
                                      let result ← (FPConvertNaN (← (FPProcessNaN__1 type3 op3 fpcr fpexc)) (Sail.BitVec.length result))
                                      (pure (done, result)))
                                  else
                                    (do
                                      let (done, result) ← (( do
                                        if ((BEq.beq type1 FPType_QNaN) : Bool)
                                        then
                                          (do
                                            let done : Bool := true
                                            let result ← (FPProcessNaN__1 type1 op1 fpcr fpexc)
                                            (pure (done, result)))
                                        else
                                          (do
                                            let (done, result) ← (( do
                                              if ((BEq.beq type2 FPType_QNaN) : Bool)
                                              then
                                                (do
                                                  let done : Bool := true
                                                  let result ← (FPConvertNaN (← (FPProcessNaN__1 type2 op2 fpcr fpexc)) (Sail.BitVec.length result))
                                                  (pure (done, result)))
                                              else
                                                (do
                                                  let (done, result) ← (( do
                                                    if ((BEq.beq type3 FPType_QNaN) : Bool)
                                                    then
                                                      (do
                                                        let done : Bool := true
                                                        let result ← (FPConvertNaN (← (FPProcessNaN__1 type3 op3 fpcr fpexc)) (Sail.BitVec.length result))
                                                        (pure (done, result)))
                                                    else
                                                      (let done : Bool := false
                                                      let result : (BitVec k_N) := (Zeros (n := (Sail.BitVec.length result)))
                                                      (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                                  (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                            (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                      (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                          (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                    (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
              (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
        (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
  (pure (done, result))

def CheckStreamingSVEEnabled (_ : Unit) : SailM Unit := do
  (CheckSMEEnabled ())
  if (((← readReg PSTATE).SM == 0#1) : Bool)
  then (SMEAccessTrap SMEExceptionType_NotStreaming (← readReg PSTATE).EL)
  else (pure ())

def CheckSMEAndZAEnabled (_ : Unit) : SailM Unit := do
  (CheckSMEEnabled ())
  if (((← readReg PSTATE).ZA == 0#1) : Bool)
  then (SMEAccessTrap SMEExceptionType_InactiveZA (← readReg PSTATE).EL)
  else (pure ())

/-- Type quantifiers: N : Nat, k_fpexc : Bool, N = 32 -/
def FPRoundBF (op : real) (fpcr : (BitVec 64)) (rounding : FPRounding) (fpexc : Bool) (N : Nat) : SailM (BitVec N) := do
  sail_assert (N == 32) "src/v8_base.sail:32210.18-32210.19"
  let isbfloat16 : Bool := true
  (FPRoundBase__1 op fpcr rounding isbfloat16 fpexc N)

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 32 -/
def FPProcessNaNs4 (type1 : FPType) (type2 : FPType) (type3 : FPType) (type4 : FPType) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (op3 : (BitVec (k_N / 2))) (op4 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  sail_assert (SPEMaxCounters == 32) "src/v8_base.sail:32270.19-32270.20"
  let result ← (( do (undefined_bitvector SPEMaxCounters) ) : SailM (BitVec k_N) )
  let done ← (( do (undefined_bool ()) ) : SailM Bool )
  let (done, result) ← (( do
    if ((BEq.beq type1 FPType_SNaN) : Bool)
    then
      (do
        let done : Bool := true
        let result ← (FPConvertNaN (← (FPProcessNaN__1 type1 op1 fpcr fpexc)) (Sail.BitVec.length result))
        (pure (done, result)))
    else
      (do
        let (done, result) ← (( do
          if ((BEq.beq type2 FPType_SNaN) : Bool)
          then
            (do
              let done : Bool := true
              let result ← (FPConvertNaN (← (FPProcessNaN__1 type2 op2 fpcr fpexc)) (Sail.BitVec.length result))
              (pure (done, result)))
          else
            (do
              let (done, result) ← (( do
                if ((BEq.beq type3 FPType_SNaN) : Bool)
                then
                  (do
                    let done : Bool := true
                    let result ← (FPConvertNaN (← (FPProcessNaN__1 type3 op3 fpcr fpexc)) (Sail.BitVec.length result))
                    (pure (done, result)))
                else
                  (do
                    let (done, result) ← (( do
                      if ((BEq.beq type4 FPType_SNaN) : Bool)
                      then
                        (do
                          let done : Bool := true
                          let result ← (FPConvertNaN (← (FPProcessNaN__1 type4 op4 fpcr fpexc)) (Sail.BitVec.length result))
                          (pure (done, result)))
                      else
                        (do
                          let (done, result) ← (( do
                            if ((BEq.beq type1 FPType_QNaN) : Bool)
                            then
                              (do
                                let done : Bool := true
                                let result ← (FPConvertNaN (← (FPProcessNaN__1 type1 op1 fpcr fpexc)) (Sail.BitVec.length result))
                                (pure (done, result)))
                            else
                              (do
                                let (done, result) ← (( do
                                  if ((BEq.beq type2 FPType_QNaN) : Bool)
                                  then
                                    (do
                                      let done : Bool := true
                                      let result ← (FPConvertNaN (← (FPProcessNaN__1 type2 op2 fpcr fpexc)) (Sail.BitVec.length result))
                                      (pure (done, result)))
                                  else
                                    (do
                                      let (done, result) ← (( do
                                        if ((BEq.beq type3 FPType_QNaN) : Bool)
                                        then
                                          (do
                                            let done : Bool := true
                                            let result ← (FPConvertNaN (← (FPProcessNaN__1 type3 op3 fpcr fpexc)) (Sail.BitVec.length result))
                                            (pure (done, result)))
                                        else
                                          (do
                                            let (done, result) ← (( do
                                              if ((BEq.beq type4 FPType_QNaN) : Bool)
                                              then
                                                (do
                                                  let done : Bool := true
                                                  let result ← (FPConvertNaN (← (FPProcessNaN__1 type4 op4 fpcr fpexc)) (Sail.BitVec.length result))
                                                  (pure (done, result)))
                                              else
                                                (let done : Bool := false
                                                let result : (BitVec k_N) := (Zeros (n := (Sail.BitVec.length result)))
                                                (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                            (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                      (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                                (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                          (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
                    (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
              (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
        (pure (done, result))) ) : SailM (Bool × (BitVec k_N)) )
  (pure (done, result))

/-- Type quantifiers: k_N : Nat, k_honor_altfp : Bool, k_N = 16 -/
def BFNeg__1 (op : (BitVec k_N)) (honor_altfp : Bool) : SailM (BitVec k_N) := SailME.run do
  let fptype ← (( do (undefined_FPType ()) ) : SailME (BitVec k_N) FPType )
  sail_assert ((Sail.BitVec.length op) == 16) "src/v8_base.sail:32449.19-32449.20"
  if ((←((pure honor_altfp) <&&> (do
       (pure (! (← (UsingAArch32 ()))))) <&&> (do
       (HaveAltFP ())))) : Bool)
  then
    (do
      let fpcr ← (( do (FPCR_read ()) ) : SailME (BitVec k_N) FPCRType )
      if (((_get_FPCRType_AH fpcr) == 1#1) : Bool)
      then
        (do
          let fpexc : Bool := false
          let isbfloat16 : Bool := true
          let fptype ← (( do
            let (__tup_0, _, _) ← do (FPUnpackBase__1 op fpcr fpexc isbfloat16)
            (pure __tup_0) ) : SailME (BitVec k_N) FPType )
          if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
          then SailME.throw (op : (BitVec k_N))
          else (pure ()))
      else (pure ()))
  else (pure ())
  (pure ((Complement.complement (BitVec.join1 [(BitVec.access op ((Sail.BitVec.length op) -i 1))])) +++ (Sail.BitVec.extractLsb op ((Sail.BitVec.length op) -i 2) 0)))


