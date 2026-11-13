import Armv9.Prelude
import Armv9.Reset
import Armv9.Fetch

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

def COLD_RESET : Bool := true

def step_model (_ : Unit) : SailM Unit := do
  writeReg SEE (Neg.neg 1)
  (__TopLevel ())
  (__CycleEnd ())

def isla_main_hook (_ : Unit) : Unit :=
  ()

def sail_main (_ : Unit) : SailM Unit := do
  sailTryCatch ((do
      let verbosity ← do (__GetVerbosity ())
      (__InitSystem ())
      let _ : Unit := (isla_main_hook ())
      (cycle_count ())
      let mut loop_vars := ()
      while (λ _ => true) loop_vars do
        let () := loop_vars
        loop_vars ← do
          if (((BitVec.access verbosity 0) == 1#1) : Bool)
          then
            (do
              let nzcv ← do (pure ((← readReg PSTATE).N +++ ((← readReg PSTATE).Z +++ ((← readReg PSTATE).C +++ (← readReg PSTATE).V))))
              (pure (print (HAppend.hAppend "[Sail] " (HAppend.hAppend (dec_str (← (get_cycle_count ()))) (HAppend.hAppend " PC=" (HAppend.hAppend (hex_str (BitVec.toNat (← readReg _PC))) (HAppend.hAppend " NZCV=" (HAppend.hAppend (hex_str (BitVec.toNat nzcv)) "
")))))))))
          else (pure ())
          (step_model ())
          if (((BitVec.access verbosity 1) == 1#1) : Bool)
          then
            (pure (print
                (HAppend.hAppend "[Sail] Instr="
                  (HAppend.hAppend (hex_str (BitVec.toNat (← readReg __ThisInstr)))
                    (HAppend.hAppend " ESR_EL3="
                      (HAppend.hAppend (hex_str (BitVec.toNat (← readReg ESR_EL3)))
                        (HAppend.hAppend
                          (← (do
                            if ((← readReg __BranchTaken) : Bool)
                            then (pure " branch taken")
                            else (pure ""))) "
")))))))
          else (pure ())
          (cycle_count ())
      (pure loop_vars))) (fun the_exception => 
    match the_exception with
      | .Error_ImplementationDefined s => (pure (print (HAppend.hAppend "Unsupported implementation defined behaviour: " s)))
      | e => (sailThrow (e) : SailM Unit))

