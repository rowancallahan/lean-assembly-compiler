import Armv9.Prelude
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

def AArch64_PendingUnmaskedVirtualInterrupts (mask_in : (BitVec 3)) : SailM (Bool × Bool × Bool) := do
  let allintmask ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let mask : (BitVec 3) := mask_in
  let pending ← (( do (undefined_bitvector 3) ) : SailM (BitVec 3) )
  let (mask, pending) ← (( do
    if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
         (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
         (EL2Enabled ())) <&&> (do
         (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1))))) : Bool)
    then
      (do
        let pending ← (pure (((_get_HCR_EL2_Type_VSE (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_VI (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_VF (← readReg HCR_EL2)))) &&& ((_get_HCR_EL2_Type_AMO (← readReg HCR_EL2)) +++ ((_get_HCR_EL2_Type_IMO (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_FMO (← readReg HCR_EL2))))))
        let mask ← (( do
          if ((←((HaveFeatNMI ()) <&&> (do
               (pure ((_get_SCTLRType_NMI (← (SCTLR_read__1 ()))) == 1#1))))) : Bool)
          then
            (do
              let allintmask ← (( do (pure ((← readReg PSTATE).ALLINT ||| ((← readReg PSTATE).SP &&& (_get_SCTLRType_SPINTMASK (← (SCTLR_read__1 ())))))) ) : SailM (BitVec 1) )
              let mask ← (( do
                if ((←((IsHCRXEL2Enabled ()) <&&> (do
                     (pure (((← readReg PSTATE).EL == EL0) || (allintmask == 0#1)))))) : Bool)
                then
                  (do
                    let mask ← (( do
                      if (((_get_HCRX_EL2_Type_VFNMI (← readReg HCRX_EL2)) == 1#1) : Bool)
                      then (pure (BitVec.update mask 0 (Bit 0#1)))
                      else (pure mask) ) : SailM (BitVec 3) )
                    if (((_get_HCRX_EL2_Type_VINMI (← readReg HCRX_EL2)) == 1#1) : Bool)
                    then (pure (BitVec.update mask 1 (Bit 0#1)))
                    else (pure mask))
                else (pure mask) ) : SailM (BitVec 3) )
              if ((((← readReg PSTATE).EL == EL1) && (allintmask == 1#1)) : Bool)
              then
                (do
                  let mask ← (( do
                    if (((_get_HCR_EL2_Type_FMO (← readReg HCR_EL2)) == 1#1) : Bool)
                    then (pure (BitVec.update mask 0 (Bit 1#1)))
                    else (pure mask) ) : SailM (BitVec 3) )
                  if (((_get_HCR_EL2_Type_IMO (← readReg HCR_EL2)) == 1#1) : Bool)
                  then (pure (BitVec.update mask 1 (Bit 1#1)))
                  else (pure mask))
              else (pure mask))
          else (pure mask) ) : SailM (BitVec 3) )
        (pure (mask, pending)))
    else
      (let pending : (BitVec 3) := 0b000#3
      (pure (mask, pending))) ) : SailM ((BitVec 3) × (BitVec 3)) )
  let unmasked_pending : (BitVec 3) := (pending &&& (Complement.complement mask))
  (pure (((BitVec.join1 [(BitVec.access unmasked_pending 2)]) == 1#1), ((BitVec.join1 [(BitVec.access unmasked_pending 1)]) == 1#1), ((BitVec.join1 [(BitVec.access unmasked_pending 0)]) == 1#1)))

def AArch32_PendingUnmaskedVirtualInterrupts (_ : Unit) : SailM (Bool × Bool × Bool) := do
  if ((←((pure (HaveEL EL2)) <&&> (do
       (pure (! (← (ELUsingAArch32 EL2))))) <||> (do
       (pure (HaveEL EL3)) <&&> (do
         (pure (! (← (ELUsingAArch32 EL3)))))))) : Bool)
  then (AArch64_PendingUnmaskedVirtualInterrupts ((← readReg PSTATE).A +++ ((← readReg PSTATE).I +++ (← readReg PSTATE).F)))
  else
    (do
      let mask ← (( do (pure ((← readReg PSTATE).A +++ ((← readReg PSTATE).I +++ (← readReg PSTATE).F))) ) : SailM (BitVec 3) )
      let pending ← (( do (undefined_bitvector 3) ) : SailM (BitVec 3) )
      let pending ← (( do
        if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
             (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 0#1))))) : Bool)
        then (do (pure (((_get_HCR_Type_VA (← (HCR_read ()))) +++ ((_get_HCR_Type_VI (← (HCR_read ()))) +++ (_get_HCR_Type_VF (← (HCR_read ()))))) &&& ((_get_HCR_Type_AMO (← (HCR_read ()))) +++ ((_get_HCR_Type_IMO (← (HCR_read ()))) +++ (_get_HCR_Type_FMO (← (HCR_read ()))))))))
        else (pure 0b000#3) ) : SailM (BitVec 3) )
      let unmasked_pending : (BitVec 3) := (pending &&& (Complement.complement mask))
      (pure (((BitVec.join1 [(BitVec.access unmasked_pending 2)]) == 1#1), ((BitVec.join1 [(BitVec.access unmasked_pending 1)]) == 1#1), ((BitVec.join1 [(BitVec.access unmasked_pending 0)]) == 1#1))))

def TakePendingInterrupts (interrupt_req : InterruptReq) : SailM Bool := do
  let interrupt_pend ← (( do (undefined_bool ()) ) : SailM Bool )
  let interrupt_taken ← (( do (undefined_bool ()) ) : SailM Bool )
  let vAA ← (( do (undefined_bool ()) ) : SailM Bool )
  let vIRQ ← (( do (undefined_bool ()) ) : SailM Bool )
  let vSE ← (( do (undefined_bool ()) ) : SailM Bool )
  let vFIQ ← (( do (undefined_bool ()) ) : SailM Bool )
  let AA ← (( do (undefined_bool ()) ) : SailM Bool )
  let IRQ ← (( do (undefined_bool ()) ) : SailM Bool )
  let FIQ ← (( do (undefined_bool ()) ) : SailM Bool )
  let SE ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((← (UsingAArch32 ())) : Bool)
  then
    (do
      let (vAA, vFIQ, vIRQ) ← (( do
        let (tup__0, tup__1, tup__2) ← do (AArch32_PendingUnmaskedVirtualInterrupts ())
        let vAA : Bool := tup__0
        let vIRQ : Bool := tup__1
        let vFIQ : Bool := tup__2
        (pure (vAA, vFIQ, vIRQ)) ) : SailM (Bool × Bool × Bool) )
      let (AA, FIQ, IRQ) ← (( do
        let (tup__0, tup__1, tup__2) ← do (AArch32_PendingUnmaskedPhysicalInterrupts ())
        let AA : Bool := tup__0
        let IRQ : Bool := tup__1
        let FIQ : Bool := tup__2
        (pure (AA, FIQ, IRQ)) ) : SailM (Bool × Bool × Bool) )
      let AA : Bool :=
        if ((! interrupt_req.take_SE) : Bool)
        then false
        else AA
      let vAA : Bool :=
        if ((! interrupt_req.take_vSE) : Bool)
        then false
        else vAA
      let IRQ : Bool :=
        if ((! interrupt_req.take_IRQ) : Bool)
        then false
        else IRQ
      let vIRQ : Bool :=
        if ((! interrupt_req.take_vIRQ) : Bool)
        then false
        else vIRQ
      let FIQ : Bool :=
        if ((! interrupt_req.take_FIQ) : Bool)
        then false
        else FIQ
      let vFIQ : Bool :=
        if ((! interrupt_req.take_vFIQ) : Bool)
        then false
        else vFIQ
      let interrupt_taken : Bool :=
        if ((((((AA || FIQ) || IRQ) || vAA) || vFIQ) || vIRQ) : Bool)
        then true
        else false
      if (vFIQ : Bool)
      then (AArch32_TakeVirtualFIQException ())
      else
        (do
          if (vIRQ : Bool)
          then (AArch32_TakeVirtualIRQException ())
          else
            (do
              if (vAA : Bool)
              then (AArch32_TakeVirtualSErrorException ())
              else
                (do
                  if (FIQ : Bool)
                  then (AArch32_TakePhysicalFIQException ())
                  else
                    (do
                      if (IRQ : Bool)
                      then (AArch32_TakePhysicalIRQException ())
                      else
                        (do
                          if (AA : Bool)
                          then (AArch32_TakePhysicalSErrorException interrupt_req.iesb_req)
                          else (pure ()))))))
      (pure interrupt_taken))
  else
    (do
      let (vFIQ, vIRQ, vSE) ← (( do
        let (tup__0, tup__1, tup__2) ← do (AArch64_PendingUnmaskedVirtualInterrupts ((← readReg PSTATE).A +++ ((← readReg PSTATE).I +++ (← readReg PSTATE).F)))
        let vSE : Bool := tup__0
        let vIRQ : Bool := tup__1
        let vFIQ : Bool := tup__2
        (pure (vFIQ, vIRQ, vSE)) ) : SailM (Bool × Bool × Bool) )
      let (FIQ, IRQ, SE) ← (( do
        let (tup__0, tup__1, tup__2) ← do (AArch64_PendingUnmaskedPhysicalInterrupts ((← readReg PSTATE).A +++ ((← readReg PSTATE).I +++ (← readReg PSTATE).F)))
        let SE : Bool := tup__0
        let IRQ : Bool := tup__1
        let FIQ : Bool := tup__2
        (pure (FIQ, IRQ, SE)) ) : SailM (Bool × Bool × Bool) )
      let SE : Bool :=
        if ((! interrupt_req.take_SE) : Bool)
        then false
        else SE
      let vSE : Bool :=
        if ((! interrupt_req.take_vSE) : Bool)
        then false
        else vSE
      let IRQ : Bool :=
        if ((! interrupt_req.take_IRQ) : Bool)
        then false
        else IRQ
      let vIRQ : Bool :=
        if ((! interrupt_req.take_vIRQ) : Bool)
        then false
        else vIRQ
      let FIQ : Bool :=
        if ((! interrupt_req.take_FIQ) : Bool)
        then false
        else FIQ
      let vFIQ : Bool :=
        if ((! interrupt_req.take_vFIQ) : Bool)
        then false
        else vFIQ
      let (FIQ, IRQ, SE, interrupt_taken, vFIQ, vIRQ, vSE) ← (( do
        if ((((((SE || FIQ) || IRQ) || vSE) || vFIQ) || vIRQ) : Bool)
        then
          (do
            let (FIQ, IRQ, SE, vFIQ, vIRQ, vSE) ← (( do
              if ((←((HaveTME ()) <&&> (do
                   (pure ((← readReg TSTATE).depth >b 0))))) : Bool)
              then
                (do
                  let (vFIQ, vIRQ, vSE) ← (( do
                    let (tup__0, tup__1, tup__2) ← do (AArch64_PendingUnmaskedVirtualInterrupts ((← readReg TSTATE).A +++ ((← readReg TSTATE).I +++ (← readReg TSTATE).F)))
                    let vSE : Bool := tup__0
                    let vIRQ : Bool := tup__1
                    let vFIQ : Bool := tup__2
                    (pure (vFIQ, vIRQ, vSE)) ) : SailM (Bool × Bool × Bool) )
                  let (FIQ, IRQ, SE) ← (( do
                    let (tup__0, tup__1, tup__2) ← do (AArch64_PendingUnmaskedPhysicalInterrupts ((← readReg TSTATE).A +++ ((← readReg TSTATE).I +++ (← readReg TSTATE).F)))
                    let SE : Bool := tup__0
                    let IRQ : Bool := tup__1
                    let FIQ : Bool := tup__2
                    (pure (FIQ, IRQ, SE)) ) : SailM (Bool × Bool × Bool) )
                  let SE : Bool :=
                    if ((! interrupt_req.take_SE) : Bool)
                    then false
                    else SE
                  let vSE : Bool :=
                    if ((! interrupt_req.take_vSE) : Bool)
                    then false
                    else vSE
                  let IRQ : Bool :=
                    if ((! interrupt_req.take_IRQ) : Bool)
                    then false
                    else IRQ
                  let vIRQ : Bool :=
                    if ((! interrupt_req.take_vIRQ) : Bool)
                    then false
                    else vIRQ
                  let FIQ : Bool :=
                    if ((! interrupt_req.take_FIQ) : Bool)
                    then false
                    else FIQ
                  let vFIQ : Bool :=
                    if ((! interrupt_req.take_vFIQ) : Bool)
                    then false
                    else vFIQ
                  let interrupt_pend : Bool := (((((SE || FIQ) || IRQ) || vSE) || vFIQ) || vIRQ)
                  (FailTransaction__1 TMFailure_IMP interrupt_pend (! interrupt_pend) (Zeros (n := 15)))
                  (pure (FIQ, IRQ, SE, vFIQ, vIRQ, vSE)))
              else (pure (FIQ, IRQ, SE, vFIQ, vIRQ, vSE)) ) : SailM (Bool × Bool × Bool × Bool × Bool × Bool) )
            let interrupt_taken : Bool := true
            (pure (FIQ, IRQ, SE, interrupt_taken, vFIQ, vIRQ, vSE)))
        else
          (let interrupt_taken : Bool := false
          (pure (FIQ, IRQ, SE, interrupt_taken, vFIQ, vIRQ, vSE))) ) : SailM (Bool × Bool × Bool × Bool × Bool × Bool × Bool) )
      if (vFIQ : Bool)
      then (AArch64_TakeVirtualFIQException ())
      else
        (do
          if (vIRQ : Bool)
          then (AArch64_TakeVirtualIRQException ())
          else
            (do
              if (vSE : Bool)
              then (AArch64_TakeVirtualSErrorException ())
              else
                (do
                  if (FIQ : Bool)
                  then (AArch64_TakePhysicalFIQException ())
                  else
                    (do
                      if (IRQ : Bool)
                      then (AArch64_TakePhysicalIRQException ())
                      else
                        (do
                          if (SE : Bool)
                          then (AArch64_TakePhysicalSErrorException interrupt_req.iesb_req)
                          else (pure ()))))))
      (pure interrupt_taken))

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

