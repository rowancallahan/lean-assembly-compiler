import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.Prelude
import Armv9.Builtins
import Armv9.V8Base
import Armv9.Stubs
import Armv9.Interrupts
import Armv9.Impdefs
import Armv9.Sysregs

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

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADC_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) imm32 (← readReg PSTATE).C))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADC_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) shifted (← readReg PSTATE).C))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADC_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) shifted (← readReg PSTATE).C))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_i_OpA_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) imm32 0#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_i_OpT_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) imm32 0#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) shifted 0#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) shifted 0#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: d : Nat, k_setflags : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_SP_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read 13)) imm32 0#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_SP_r_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read 13)) shifted 0#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: k_add : Bool, d : Nat, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADR_Op_A_txt (add : Bool) (d : Nat) (imm32 : (BitVec 32)) : SailM Unit := do
  let result ← (( do
    if (add : Bool)
    then (pure ((Align_bits (← (PC_read__1 ())) 4) + imm32))
    else (pure ((Align_bits (← (PC_read__1 ())) 4) - imm32)) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then (ALUWritePC result)
  else (R_set d result)

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_AND_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let result ← (( do (pure ((← (R_read n)) &&& imm32)) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_AND_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) &&& shifted)) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_AND_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) &&& shifted)) ) : SailM (BitVec 32) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_ASR_i_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, result) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) SRType_ASR shift_n (← readReg PSTATE).C)
    let result : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, result)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_ASR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0)))
  let (carry, result) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read n)) SRType_ASR shift_n (← readReg PSTATE).C)
    let result : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, result)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

def execute_aarch32_instrs_B_Op_A_txt (imm32 : (BitVec 32)) : SailM Unit := do
  (BranchWritePC ((← (PC_read__1 ())) + imm32) BranchType_DIR)

/-- Type quantifiers: d : Nat, lsbit : Nat, msbit : Nat, 0 ≤ msbit ∧ msbit ≤ 31 ∧ 0 ≤ lsbit ∧ lsbit ≤ 31 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_BFC_Op_A_txt (d : Nat) (lsbit : Nat) (msbit : Nat) : SailM Unit := do
  sail_assert (lsbit ≤b msbit) "src/instrs32.sail:1519.39-1519.40"
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) msbit lsbit (BitVec.replicateBits 0#1 ((msbit -i lsbit) +i 1))))

/-- Type quantifiers: d : Nat, lsbit : Nat, msbit : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ msbit ∧ msbit ≤ 31 ∧ 0 ≤ lsbit ∧ lsbit ≤ 31 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_BFI_Op_A_txt (d : Nat) (lsbit : Nat) (msbit : Nat) (n : Nat) : SailM Unit := do
  sail_assert (0 ≤b (msbit -i lsbit)) "src/instrs32.sail:1587.43-1587.44"
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) msbit lsbit (Sail.BitVec.extractLsb (← (R_read n)) (msbit -i lsbit) 0)))

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_BIC_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let result ← (( do (pure ((← (R_read n)) &&& (Complement.complement imm32))) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_BIC_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) &&& (Complement.complement shifted))) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_BIC_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) &&& (Complement.complement shifted))) ) : SailM (BitVec 32) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

def execute_aarch32_instrs_BKPT_Op_A_txt (imm16 : (BitVec 16)) : SailM Unit := do
  (AArch32_SoftwareBreakpoint imm16)

def execute_aarch32_instrs_BL_i_Op_A_txt (imm32 : (BitVec 32)) (targetInstrSet : InstrSet) : SailM Unit := do
  if ((BEq.beq (← (CurrentInstrSet ())) InstrSet_A32) : Bool)
  then (LR_write (BitVec.subInt (← (PC_read__1 ())) 4))
  else (LR_write ((Sail.BitVec.extractLsb (← (PC_read__1 ())) 31 1) +++ 1#1))
  let targetAddress ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let targetAddress ← (( do
    if ((BEq.beq targetInstrSet InstrSet_A32) : Bool)
    then (do (pure ((Align_bits (← (PC_read__1 ())) 4) + imm32)))
    else (do (pure ((← (PC_read__1 ())) + imm32))) ) : SailM (BitVec 32) )
  (SelectInstrSet targetInstrSet)
  (BranchWritePC targetAddress BranchType_DIRCALL)

/-- Type quantifiers: m : Nat, 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_BLX_r_Op_A_txt (m : Nat) : SailM Unit := do
  let target ← (( do (R_read m) ) : SailM (BitVec 32) )
  let next_instr_addr ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  if ((BEq.beq (← (CurrentInstrSet ())) InstrSet_A32) : Bool)
  then
    (do
      let next_instr_addr ← (( do (pure (BitVec.subInt (← (PC_read__1 ())) 4)) ) : SailM (BitVec 32) )
      (LR_write next_instr_addr))
  else
    (do
      let next_instr_addr ← (( do (pure (BitVec.subInt (← (PC_read__1 ())) 2)) ) : SailM (BitVec 32) )
      (LR_write ((Sail.BitVec.extractLsb next_instr_addr 31 1) +++ 1#1)))
  (BXWritePC target BranchType_INDCALL)

/-- Type quantifiers: m : Nat, 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_BX_Op_A_txt (m : Nat) : SailM Unit := do
  (BXWritePC (← (R_read m)) BranchType_INDIR)

/-- Type quantifiers: m : Nat, 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_BXJ_Op_A_txt (m : Nat) : SailM Unit := do
  (BXWritePC (← (R_read m)) BranchType_INDIR)

/-- Type quantifiers: n : Nat, k_nonzero : Bool, List.elem n [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_CBNZ_Op_A_txt (imm32 : (BitVec 32)) (n : Nat) (nonzero : Bool) : SailM Unit := do
  if ((neq_bool nonzero (IsZero (← (R_read n)))) : Bool)
  then (CBWritePC ((← (PC_read__1 ())) + imm32))
  else (pure ())

def execute_aarch32_instrs_CLREX_Op_A_txt (_ : Unit) : Unit :=
  (ClearExclusiveLocal (ProcessorID ()))

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_CLZ_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let result ← do (pure (CountLeadingZeroBits (← (R_read m))))
  (R_set d (integer_subrange result 31 0))

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_CMN_i_Op_A_txt (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let nzcv ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) imm32 0#1))
    let result : (BitVec 32) := tup__0
    (pure tup__1) ) : SailM (BitVec 4) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }

/-- Type quantifiers: m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_CMN_r_Op_A_txt (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let nzcv ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) shifted 0#1))
    let result : (BitVec 32) := tup__0
    (pure tup__1) ) : SailM (BitVec 4) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }

/-- Type quantifiers: m : Nat, n : Nat, s : Nat, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_CMN_rr_Op_A_txt (m : Nat) (n : Nat) (s : Nat) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let nzcv ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) shifted 0#1))
    let result : (BitVec 32) := tup__0
    (pure tup__1) ) : SailM (BitVec 4) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_CMP_i_Op_A_txt (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let nzcv ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) (Complement.complement imm32) 1#1))
    let result : (BitVec 32) := tup__0
    (pure tup__1) ) : SailM (BitVec 4) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }

/-- Type quantifiers: m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_CMP_r_Op_A_txt (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let nzcv ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) (Complement.complement shifted) 1#1))
    let result : (BitVec 32) := tup__0
    (pure tup__1) ) : SailM (BitVec 4) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }

/-- Type quantifiers: m : Nat, n : Nat, s : Nat, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_CMP_rr_Op_A_txt (m : Nat) (n : Nat) (s : Nat) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let nzcv ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) (Complement.complement shifted) 1#1))
    let result : (BitVec 32) := tup__0
    (pure tup__1) ) : SailM (BitVec 4) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }

def execute_aarch32_instrs_DBG_Op_A_txt (_ : Unit) : Unit :=
  ()

def execute_aarch32_instrs_DMB_Op_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let domain ← (( do (undefined_MBReqDomain ()) ) : SailM MBReqDomain )
  let types ← (( do (undefined_MBReqTypes ()) ) : SailM MBReqTypes )
  let (domain, types) : (MBReqDomain × MBReqTypes) :=
    match (option_name : BitVec 4) with
    | 0b0001 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b0010 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | 0b0011 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_All
      (domain, types))
    | 0b0101 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b0110 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | 0b0111 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_All
      (domain, types))
    | 0b1001 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b1010 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | 0b1011 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_All
      (domain, types))
    | 0b1101 =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b1110 =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | _ =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_All
      (domain, types))
  let types := types
  let domain ← (( do
    if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
         (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
         (EL2Enabled ())))) : Bool)
    then
      (do
        let domain ← (( do
          if (((_get_HCR_Type_BSU (← (HCR_read ()))) == 0b11#2) : Bool)
          then (pure MBReqDomain_FullSystem)
          else (pure domain) ) : SailM MBReqDomain )
        let domain ← (( do
          if ((((_get_HCR_Type_BSU (← (HCR_read ()))) == 0b10#2) && (bne domain MBReqDomain_FullSystem)) : Bool)
          then (pure MBReqDomain_OuterShareable)
          else (pure domain) ) : SailM MBReqDomain )
        if ((((_get_HCR_Type_BSU (← (HCR_read ()))) == 0b01#2) && (BEq.beq domain MBReqDomain_Nonshareable)) : Bool)
        then (pure MBReqDomain_InnerShareable)
        else (pure domain))
    else (pure domain) ) : SailM MBReqDomain )
  (DataMemoryBarrier domain types)

def execute_aarch32_instrs_DSB_Op_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let nXS ← (( do (undefined_bool ()) ) : SailM Bool )
  let nXS ← (( do
    if ((← (HaveFeatXS ())) : Bool)
    then (do (pure ((← readReg PSTATE).EL == EL0)) <||> (do (pure ((← readReg PSTATE).EL == EL1))) <&&> (do (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do (IsHCRXEL2Enabled ())) <&&> (do (pure ((_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2)) == 1#1))))
    else (pure false) ) : SailM Bool )
  let domain ← (( do (undefined_MBReqDomain ()) ) : SailM MBReqDomain )
  let types ← (( do (undefined_MBReqTypes ()) ) : SailM MBReqTypes )
  let (domain, types) ← (( do
    match (option_name : BitVec 4) with
    | 0b0001 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_Reads
      (pure (domain, types)))
    | 0b0010 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_Writes
      (pure (domain, types)))
    | 0b0011 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_All
      (pure (domain, types)))
    | 0b0101 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_Reads
      (pure (domain, types)))
    | 0b0110 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_Writes
      (pure (domain, types)))
    | 0b0111 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_All
      (pure (domain, types)))
    | 0b1001 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_Reads
      (pure (domain, types)))
    | 0b1010 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_Writes
      (pure (domain, types)))
    | 0b1011 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_All
      (pure (domain, types)))
    | 0b1101 =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_Reads
      (pure (domain, types)))
    | 0b1110 =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_Writes
      (pure (domain, types)))
    | _ =>
      (do
        sail_assert (! (let b__0 := option_name
          if ((((Sail.BitVec.extractLsb b__0 3 3) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
          then true
          else false : Bool)) "src/instrs32.sail:3029.20-3029.21"
        let domain : MBReqDomain := MBReqDomain_FullSystem
        let types : MBReqTypes := MBReqTypes_All
        (pure (domain, types))) ) : SailM (MBReqDomain × MBReqTypes) )
  let types := types
  let domain ← (( do
    if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
         (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
         (EL2Enabled ())))) : Bool)
    then
      (do
        let domain ← (( do
          if (((_get_HCR_Type_BSU (← (HCR_read ()))) == 0b11#2) : Bool)
          then (pure MBReqDomain_FullSystem)
          else (pure domain) ) : SailM MBReqDomain )
        let domain ← (( do
          if ((((_get_HCR_Type_BSU (← (HCR_read ()))) == 0b10#2) && (bne domain MBReqDomain_FullSystem)) : Bool)
          then (pure MBReqDomain_OuterShareable)
          else (pure domain) ) : SailM MBReqDomain )
        if ((((_get_HCR_Type_BSU (← (HCR_read ()))) == 0b01#2) && (BEq.beq domain MBReqDomain_Nonshareable)) : Bool)
        then (pure MBReqDomain_InnerShareable)
        else (pure domain))
    else (pure domain) ) : SailM MBReqDomain )
  (DataSynchronizationBarrier domain types nXS)

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_EOR_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let result ← (( do (pure ((← (R_read n)) ^^^ imm32)) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_EOR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) ^^^ shifted)) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_EOR_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) ^^^ shifted)) ) : SailM (BitVec 32) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

def execute_aarch32_instrs_ISB_Op_A_txt (_ : Unit) : SailM Unit := do
  (InstructionSynchronizationBarrier ())

def execute_aarch32_instrs_IT_Op_A_txt (firstcond : (BitVec 4)) (mask : (BitVec 4)) : SailM Unit := do
  (AArch32_CheckITEnabled mask)
  writeReg PSTATE { (← readReg PSTATE) with IT := ← (do (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).IT 7 0 (firstcond +++ mask)))) }
  writeReg ShouldAdvanceIT false

/-- Type quantifiers: k_add : Bool, cp : Nat, k_index : Bool, n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ cp = 14 -/
def execute_aarch32_instrs_LDC_i_Op_A_txt (add : Bool) (cp : Nat) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SysRegWriteM cp (← (ThisInstr ())) address)
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, cp : Nat, k_index : Bool, cp = 14 -/
def execute_aarch32_instrs_LDC_l_Op_A_txt (add : Bool) (cp : Nat) (imm32 : (BitVec 32)) (index : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((Align_bits (← (PC_read__1 ())) 4) + imm32))
    else (pure ((Align_bits (← (PC_read__1 ())) 4) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (pure (Align_bits (← (PC_read__1 ())) 4)) ) : SailM (BitVec 32) )
  (AArch32_SysRegWriteM cp (← (ThisInstr ())) address)

/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDM_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 14
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
        then
          (do
            (R_set i (← (MemS_read address 4)))
            (pure (BitVec.addInt address 4)))
        else (pure address)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
  then (LoadWritePC (← (MemS_read address 4)))
  else (pure ())
  if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 0#1)) : Bool)
  then (R_set n (BitVec.addInt (← (R_read n)) (4 *i (BitCount registers))))
  else (pure ())
  if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
  then (R_set n (← (__UNKNOWN_bits 32)))
  else (pure ())

/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDMDA_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let address ← (( do (pure (BitVec.addInt (BitVec.subInt (← (R_read n)) (4 *i (BitCount registers))) 4)) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 14
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
        then
          (do
            (R_set i (← (MemS_read address 4)))
            (pure (BitVec.addInt address 4)))
        else (pure address)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
  then (LoadWritePC (← (MemS_read address 4)))
  else (pure ())
  if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 0#1)) : Bool)
  then (R_set n (BitVec.subInt (← (R_read n)) (4 *i (BitCount registers))))
  else (pure ())
  if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
  then (R_set n (← (__UNKNOWN_bits 32)))
  else (pure ())

/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDMDB_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let address ← (( do (pure (BitVec.subInt (← (R_read n)) (4 *i (BitCount registers)))) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 14
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
        then
          (do
            (R_set i (← (MemS_read address 4)))
            (pure (BitVec.addInt address 4)))
        else (pure address)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
  then (LoadWritePC (← (MemS_read address 4)))
  else (pure ())
  if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 0#1)) : Bool)
  then (R_set n (BitVec.subInt (← (R_read n)) (4 *i (BitCount registers))))
  else (pure ())
  if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
  then (R_set n (← (__UNKNOWN_bits 32)))
  else (pure ())

/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDMIB_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let address ← (( do (pure (BitVec.addInt (← (R_read n)) 4)) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 14
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
        then
          (do
            (R_set i (← (MemS_read address 4)))
            (pure (BitVec.addInt address 4)))
        else (pure address)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
  then (LoadWritePC (← (MemS_read address 4)))
  else (pure ())
  if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 0#1)) : Bool)
  then (R_set n (BitVec.addInt (← (R_read n)) (4 *i (BitCount registers))))
  else (pure ())
  if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
  then (R_set n (← (__UNKNOWN_bits 32)))
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRB_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  (R_set t (Sail.BitVec.zeroExtend (← (MemU_read address 1)) 32))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRB_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  (R_set t (Sail.BitVec.zeroExtend (← (MemU_read address 1)) 32))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_LDRB_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (t : Nat) : SailM Unit := do
  let base ← (( do (pure (Align_bits (← (PC_read__1 ())) 4)) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  let _ : Unit :=
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  (R_set t (Sail.BitVec.zeroExtend (← (MemU_read address 1)) 32))

/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDRB_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  (R_set t (Sail.BitVec.zeroExtend (← (MemU_read address 1)) 32))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, shift_n : Int, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRBT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (shift_n : Int) (shift_t : SRType) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let offset ← (( do
    if (register_form : Bool)
    then (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    else (pure imm32) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then (R_read n)
    else (pure offset_addr) ) : SailM (BitVec 32) )
  if ((←((pure ((! postindex) && (t != 15))) <&&> (do
       (pure ((← readReg PSTATE).T == 1#1))))) : Bool)
  then (pure (AArch32_SetLSInstructionSyndrome 1 false t false))
  else (pure ())
  (R_set t (Sail.BitVec.zeroExtend (← (MemU_unpriv_read address 1)) 32))
  if (postindex : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, t2 : Nat, k_wback : Bool, 0 ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRD_i_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (t2 : Nat) (wback : Bool) : SailM Unit := do
  let data ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  if ((IsAligned__1 address 8) : Bool)
  then
    (do
      let data ← (( do (MemA_read address 8) ) : SailM (BitVec 64) )
      if ((← (BigEndian AccessType_GPR)) : Bool)
      then
        (do
          (R_set t (Sail.BitVec.extractLsb data 63 32))
          (R_set t2 (Sail.BitVec.extractLsb data 31 0)))
      else
        (do
          (R_set t (Sail.BitVec.extractLsb data 31 0))
          (R_set t2 (Sail.BitVec.extractLsb data 63 32))))
  else
    (do
      (R_set t (← (MemA_read address 4)))
      (R_set t2 (← (MemA_read (BitVec.addInt address 4) 4))))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, t : Nat, t2 : Nat, 0 ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_LDRD_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (t : Nat) (t2 : Nat) : SailM Unit := do
  let data ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if (add : Bool)
    then (pure ((Align_bits (← (PC_read__1 ())) 4) + imm32))
    else (pure ((Align_bits (← (PC_read__1 ())) 4) - imm32)) ) : SailM (BitVec 32) )
  if ((IsAligned__1 address 8) : Bool)
  then
    (do
      let data ← (( do (MemA_read address 8) ) : SailM (BitVec 64) )
      if ((← (BigEndian AccessType_GPR)) : Bool)
      then
        (do
          (R_set t (Sail.BitVec.extractLsb data 63 32))
          (R_set t2 (Sail.BitVec.extractLsb data 31 0)))
      else
        (do
          (R_set t (Sail.BitVec.extractLsb data 31 0))
          (R_set t2 (Sail.BitVec.extractLsb data 63 32))))
  else
    (do
      (R_set t (← (MemA_read address 4)))
      (R_set t2 (← (MemA_read (BitVec.addInt address 4) 4))))

/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, t : Nat, t2 : Nat, k_wback : Bool, 1 ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDRD_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (t : Nat) (t2 : Nat) (wback : Bool) : SailM Unit := do
  let data ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + (← (R_read m))))
    else (pure ((← (R_read n)) - (← (R_read m)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  if ((IsAligned__1 address 8) : Bool)
  then
    (do
      let data ← (( do (MemA_read address 8) ) : SailM (BitVec 64) )
      if ((← (BigEndian AccessType_GPR)) : Bool)
      then
        (do
          (R_set t (Sail.BitVec.extractLsb data 63 32))
          (R_set t2 (Sail.BitVec.extractLsb data 31 0)))
      else
        (do
          (R_set t (Sail.BitVec.extractLsb data 31 0))
          (R_set t2 (Sail.BitVec.extractLsb data 63 32))))
  else
    (do
      (R_set t (← (MemA_read address 4)))
      (R_set t2 (← (MemA_read (BitVec.addInt address 4) 4))))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDREX_Op_A_txt (imm32 : (BitVec 32)) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (pure ((← (R_read n)) + imm32)) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 4)
  (R_set t (← (MemA_read address 4)))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDREXB_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 1)
  (R_set t (Sail.BitVec.zeroExtend (← (MemA_read address 1)) 32))

/-- Type quantifiers: n : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDREXD_Op_A_txt (n : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 8)
  let value_name ← (( do (MemA_read address 8) ) : SailM (BitVec 64) )
  (R_set t
    (← (do
      if ((← (BigEndian AccessType_GPR)) : Bool)
      then (pure (Sail.BitVec.extractLsb value_name 63 32))
      else (pure (Sail.BitVec.extractLsb value_name 31 0)))))
  (R_set t2
    (← (do
      if ((← (BigEndian AccessType_GPR)) : Bool)
      then (pure (Sail.BitVec.extractLsb value_name 31 0))
      else (pure (Sail.BitVec.extractLsb value_name 63 32)))))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDREXH_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 2)
  (R_set t (Sail.BitVec.zeroExtend (← (MemA_read address 2)) 32))

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRH_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())
  (R_set t (Sail.BitVec.zeroExtend data 32))

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRH_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())
  (R_set t (Sail.BitVec.zeroExtend data 32))

/-- Type quantifiers: k_add : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_LDRH_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (t : Nat) : SailM Unit := do
  let base ← (( do (pure (Align_bits (← (PC_read__1 ())) 4)) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  let _ : Unit :=
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  (R_set t (Sail.BitVec.zeroExtend data 32))

/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDRH_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())
  (R_set t (Sail.BitVec.zeroExtend data 32))

/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRHT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let offset ← (( do
    if (register_form : Bool)
    then (R_read m)
    else (pure imm32) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then (R_read n)
    else (pure offset_addr) ) : SailM (BitVec 32) )
  if ((←((pure ((! postindex) && (t != 15))) <&&> (do
       (pure ((← readReg PSTATE).T == 1#1))))) : Bool)
  then (pure (AArch32_SetLSInstructionSyndrome 2 false t false))
  else (pure ())
  let data ← (( do (MemU_unpriv_read address 2) ) : SailM (BitVec 16) )
  if (postindex : Bool)
  then (R_set n offset_addr)
  else (pure ())
  (R_set t (Sail.BitVec.zeroExtend data 32))

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDR_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  let data ← (( do (MemU_read address 4) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())
  if ((t == 15) : Bool)
  then
    (do
      if (((Sail.BitVec.extractLsb address 1 0) == 0b00#2) : Bool)
      then (LoadWritePC data)
      else (sailThrow ((Error_Unpredictable ())) : SailM Unit))
  else (R_set t data)

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDR_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  let data ← (( do (MemU_read address 4) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())
  if ((t == 15) : Bool)
  then
    (do
      if (((Sail.BitVec.extractLsb address 1 0) == 0b00#2) : Bool)
      then (LoadWritePC data)
      else (sailThrow ((Error_Unpredictable ())) : SailM Unit))
  else (R_set t data)

/-- Type quantifiers: k_add : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_LDR_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (t : Nat) : SailM Unit := do
  let base ← (( do (pure (Align_bits (← (PC_read__1 ())) 4)) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  let _ : Unit :=
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  let data ← (( do (MemU_read address 4) ) : SailM (BitVec 32) )
  if ((t == 15) : Bool)
  then
    (do
      if (((Sail.BitVec.extractLsb address 1 0) == 0b00#2) : Bool)
      then (LoadWritePC data)
      else (sailThrow ((Error_Unpredictable ())) : SailM Unit))
  else (R_set t data)

/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDR_r_OpA_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  let data ← (( do (MemU_read address 4) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())
  if ((t == 15) : Bool)
  then
    (do
      if (((Sail.BitVec.extractLsb address 1 0) == 0b00#2) : Bool)
      then (LoadWritePC data)
      else (sailThrow ((Error_Unpredictable ())) : SailM Unit))
  else (R_set t data)

/-- Type quantifiers: m : Nat, n : Nat, shift_n : Int, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDR_r_OpT_A_txt (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do (pure ((← (R_read n)) + offset)) ) : SailM (BitVec 32) )
  let address : (BitVec 32) := offset_addr
  let _ : Unit :=
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  let data ← (( do (MemU_read address 4) ) : SailM (BitVec 32) )
  if ((t == 15) : Bool)
  then
    (do
      if (((Sail.BitVec.extractLsb address 1 0) == 0b00#2) : Bool)
      then (LoadWritePC data)
      else (sailThrow ((Error_Unpredictable ())) : SailM Unit))
  else (R_set t data)

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRSB_i_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 true t false)
    else ()
  (R_set t (sign_extend (← (MemU_read address 1)) 32))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_LDRSB_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (t : Nat) : SailM Unit := do
  let base ← (( do (pure (Align_bits (← (PC_read__1 ())) 4)) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  let _ : Unit :=
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 true t false)
    else ()
  (R_set t (sign_extend (← (MemU_read address 1)) 32))

/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDRSB_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 true t false)
    else ()
  (R_set t (sign_extend (← (MemU_read address 1)) 32))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRSBT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let offset ← (( do
    if (register_form : Bool)
    then (R_read m)
    else (pure imm32) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then (R_read n)
    else (pure offset_addr) ) : SailM (BitVec 32) )
  if ((←((pure ((! postindex) && (t != 15))) <&&> (do
       (pure ((← readReg PSTATE).T == 1#1))))) : Bool)
  then (pure (AArch32_SetLSInstructionSyndrome 1 true t false))
  else (pure ())
  (R_set t (sign_extend (← (MemU_unpriv_read address 1)) 32))
  if (postindex : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRSH_i_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 true t false)
    else ()
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())
  (R_set t (sign_extend data 32))

/-- Type quantifiers: k_add : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_LDRSH_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (t : Nat) : SailM Unit := do
  let base ← (( do (pure (Align_bits (← (PC_read__1 ())) 4)) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  let _ : Unit :=
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 true t false)
    else ()
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  (R_set t (sign_extend data 32))

/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDRSH_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 true t false)
    else ()
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())
  (R_set t (sign_extend data 32))

/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRSHT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let offset ← (( do
    if (register_form : Bool)
    then (R_read m)
    else (pure imm32) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then (R_read n)
    else (pure offset_addr) ) : SailM (BitVec 32) )
  if ((←((pure ((! postindex) && (t != 15))) <&&> (do
       (pure ((← readReg PSTATE).T == 1#1))))) : Bool)
  then (pure (AArch32_SetLSInstructionSyndrome 2 true t false))
  else (pure ())
  let data ← (( do (MemU_unpriv_read address 2) ) : SailM (BitVec 16) )
  if (postindex : Bool)
  then (R_set n offset_addr)
  else (pure ())
  (R_set t (sign_extend data 32))

/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, shift_n : Int, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (shift_n : Int) (shift_t : SRType) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let offset ← (( do
    if (register_form : Bool)
    then (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    else (pure imm32) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then (R_read n)
    else (pure offset_addr) ) : SailM (BitVec 32) )
  if ((←((pure ((! postindex) && (t != 15))) <&&> (do
       (pure ((← readReg PSTATE).T == 1#1))))) : Bool)
  then (pure (AArch32_SetLSInstructionSyndrome 4 false t false))
  else (pure ())
  let data ← (( do (MemU_unpriv_read address 4) ) : SailM (BitVec 32) )
  if (postindex : Bool)
  then (R_set n offset_addr)
  else (pure ())
  (R_set t data)

/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_LSL_i_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, result) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) SRType_LSL shift_n (← readReg PSTATE).C)
    let result : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, result)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_LSL_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0)))
  let (carry, result) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read n)) SRType_LSL shift_n (← readReg PSTATE).C)
    let result : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, result)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_LSR_i_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, result) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) SRType_LSR shift_n (← readReg PSTATE).C)
    let result : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, result)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_LSR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0)))
  let (carry, result) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read n)) SRType_LSR shift_n (← readReg PSTATE).C)
    let result : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, result)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: cp : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ List.elem cp [14, 15] -/
def execute_aarch32_instrs_MCR_Op_A_txt (cp : Nat) (t : Nat) : SailM Unit := do
  (AArch32_SysRegWrite cp (← (ThisInstr ())) t)

/-- Type quantifiers: cp : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧ t2 ≤ 15 ∧ 0 ≤ t ∧ t ≤ 15 ∧ List.elem cp [14, 15] -/
def execute_aarch32_instrs_MCRR_Op_A_txt (cp : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  (AArch32_SysRegWrite64 cp (← (ThisInstr ())) t t2)

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_MLA_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let operand1 ← do (pure (BitVec.toInt (← (R_read n))))
  let operand2 ← do (pure (BitVec.toInt (← (R_read m))))
  let addend ← do (pure (BitVec.toInt (← (R_read a))))
  let result := ((operand1 *i operand2) +i addend)
  (R_set d (integer_subrange result 31 0))
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(integer_access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit (integer_subrange result 31 0)) })
  else (pure ())

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_MLS_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← do (pure (BitVec.toInt (← (R_read n))))
  let operand2 ← do (pure (BitVec.toInt (← (R_read m))))
  let addend ← do (pure (BitVec.toInt (← (R_read a))))
  let result := (addend -i (operand1 *i operand2))
  (R_set d (integer_subrange result 31 0))

/-- Type quantifiers: d : Nat, k_setflags : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MOV_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (setflags : Bool) : SailM Unit := do
  let result : (BitVec 32) := imm32
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MOV_r_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result : (BitVec 32) := shifted
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MOV_rr_Op_A_txt (d : Nat) (m : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let (carry, result) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let result : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, result)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: d : Nat, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MOVT_Op_A_txt (d : Nat) (imm16 : (BitVec 16)) : SailM Unit := do
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 imm16))

/-- Type quantifiers: cp : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ List.elem cp [14, 15] -/
def execute_aarch32_instrs_MRC_Op_A_txt (cp : Nat) (t : Nat) : SailM Unit := do
  if ((←((pure (t != 15)) <||> (do
       (AArch32_SysRegReadCanWriteAPSR cp (← (ThisInstr ())))))) : Bool)
  then (AArch32_SysRegRead__1 cp (← (ThisInstr ())) t)
  else (sailThrow ((Error_Unpredictable ())) : SailM Unit)

/-- Type quantifiers: cp : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧ t2 ≤ 15 ∧ 0 ≤ t ∧ t ≤ 15 ∧ List.elem cp [14, 15] -/
def execute_aarch32_instrs_MRRC_Op_A_txt (cp : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  (AArch32_SysRegRead64 cp (← (ThisInstr ())) t t2)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MUL_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let operand1 ← do (pure (BitVec.toInt (← (R_read n))))
  let operand2 ← do (pure (BitVec.toInt (← (R_read m))))
  let result := (operand1 *i operand2)
  (R_set d (integer_subrange result 31 0))
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(integer_access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit (integer_subrange result 31 0)) })
  else (pure ())

/-- Type quantifiers: d : Nat, k_setflags : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MVN_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (setflags : Bool) : SailM Unit := do
  let result : (BitVec 32) := (Complement.complement imm32)
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MVN_r_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result : (BitVec 32) := (Complement.complement shifted)
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MVN_rr_Op_A_txt (d : Nat) (m : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result : (BitVec 32) := (Complement.complement shifted)
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

def execute_aarch32_instrs_NOP_Op_A_txt (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ORN_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let result ← (( do (pure ((← (R_read n)) ||| (Complement.complement imm32))) ) : SailM (BitVec 32) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ORN_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) ||| (Complement.complement shifted))) ) : SailM (BitVec 32) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ORR_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let result ← (( do (pure ((← (R_read n)) ||| imm32)) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ORR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) ||| shifted)) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
          writeReg PSTATE { (← readReg PSTATE) with C := carry })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ORR_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) ||| shifted)) ) : SailM (BitVec 32) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, shift_n : Int, k_tbform : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_PKH_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (tbform : Bool) : SailM Unit := do
  let operand2 ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.updateSubrange (← (R_read d)) 15 0
      (← (do
        if (tbform : Bool)
        then (pure (Sail.BitVec.extractLsb operand2 15 0))
        else (pure (Sail.BitVec.extractLsb (← (R_read n)) 15 0))))))
  (R_set d
    (Sail.BitVec.updateSubrange (← (R_read d)) 31 16
      (← (do
        if (tbform : Bool)
        then (pure (Sail.BitVec.extractLsb (← (R_read n)) 31 16))
        else (pure (Sail.BitVec.extractLsb operand2 31 16))))))

/-- Type quantifiers: k_add : Bool, k_is_pldw : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_PLD_i_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (is_pldw : Bool) (n : Nat) : SailM Unit := do
  let address ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  if (is_pldw : Bool)
  then (pure (Hint_PreloadDataForWrite address))
  else (pure (Hint_PreloadData address))

/-- Type quantifiers: k_add : Bool -/
def execute_aarch32_instrs_PLD_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) : SailM Unit := do
  let address ← (( do
    if (add : Bool)
    then (pure ((Align_bits (← (PC_read__1 ())) 4) + imm32))
    else (pure ((Align_bits (← (PC_read__1 ())) 4) - imm32)) ) : SailM (BitVec 32) )
  (pure (Hint_PreloadData address))

/-- Type quantifiers: k_add : Bool, k_is_pldw : Bool, m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_PLD_r_Op_A_txt (add : Bool) (is_pldw : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let address ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  if (is_pldw : Bool)
  then (pure (Hint_PreloadDataForWrite address))
  else (pure (Hint_PreloadData address))

/-- Type quantifiers: k_add : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_PLI_i_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let base ← (( do
    if ((n == 15) : Bool)
    then (pure (Align_bits (← (PC_read__1 ())) 4))
    else (R_read n) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  (pure (Hint_PreloadInstr address))

/-- Type quantifiers: k_add : Bool, m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_PLI_r_Op_A_txt (add : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let address ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  (pure (Hint_PreloadInstr address))

/-- Type quantifiers: k_UnalignedAllowed : Bool -/
def execute_aarch32_instrs_POP_Op_A_txt (UnalignedAllowed : Bool) (registers : (BitVec 16)) : SailM Unit := do
  let address ← (( do (R_read 13) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 14
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
        then
          (do
            (R_set i
              (← (do
                if (UnalignedAllowed : Bool)
                then (MemU_read address 4)
                else (MemA_read address 4))))
            (pure (BitVec.addInt address 4)))
        else (pure address)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
  then
    (do
      if (UnalignedAllowed : Bool)
      then
        (do
          if (((Sail.BitVec.extractLsb address 1 0) == 0b00#2) : Bool)
          then (LoadWritePC (← (MemU_read address 4)))
          else (sailThrow ((Error_Unpredictable ())) : SailM Unit))
      else (LoadWritePC (← (MemA_read address 4))))
  else (pure ())
  if (((BitVec.join1 [(BitVec.access registers 13)]) == 0#1) : Bool)
  then (R_set 13 (BitVec.addInt (← (R_read 13)) (4 *i (BitCount registers))))
  else (pure ())
  if (((BitVec.join1 [(BitVec.access registers 13)]) == 1#1) : Bool)
  then (R_set 13 (← (__UNKNOWN_bits 32)))
  else (pure ())

/-- Type quantifiers: k_UnalignedAllowed : Bool -/
def execute_aarch32_instrs_PUSH_Op_A_txt (UnalignedAllowed : Bool) (registers : (BitVec 16)) : SailM Unit := do
  let address ← (( do (pure (BitVec.subInt (← (R_read 13)) (4 *i (BitCount registers)))) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 14
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
        then
          (do
            if (((i == 13) && (i != (LowestSetBit registers))) : Bool)
            then (MemA_set address 4 (← (__UNKNOWN_bits 32)))
            else
              (do
                if (UnalignedAllowed : Bool)
                then (MemU_set address 4 (← (R_read i)))
                else (MemA_set address 4 (← (R_read i))))
            (pure (BitVec.addInt address 4)))
        else (pure address)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
  then
    (do
      if (UnalignedAllowed : Bool)
      then (MemU_set address 4 (← (PCStoreValue ())))
      else (MemA_set address 4 (← (PCStoreValue ()))))
  else (pure ())
  (R_set 13 (BitVec.subInt (← (R_read 13)) (4 *i (BitCount registers))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let sum2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (← (SignedSat sum1 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (← (SignedSat sum2 16))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let sum2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let sum3 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let sum4 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (← (SignedSat sum1 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (← (SignedSat sum2 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (← (SignedSat sum3 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (← (SignedSat sum4 8))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QADD_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let sat ← (( do
    let (__tup_0, __tup_1) ← do (SignedSatQ ((BitVec.toInt (← (R_read m))) +i (BitVec.toInt (← (R_read n)))) 32)
    (R_set d __tup_0)
    (pure __tup_1) ) : SailM Bool )
  if (sat : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let sum ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (← (SignedSat diff 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (← (SignedSat sum 16))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QDADD_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let doubled ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let sat1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let (doubled, sat1) ← (( do
    let (tup__0, tup__1) ← do (SignedSatQ (2 *i (BitVec.toInt (← (R_read n)))) 32)
    let doubled : (BitVec 32) := tup__0
    let sat1 : Bool := tup__1
    (pure (doubled, sat1)) ) : SailM ((BitVec 32) × Bool) )
  let sat2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let sat2 ← (( do
    let (__tup_0, __tup_1) ← do (SignedSatQ ((BitVec.toInt (← (R_read m))) +i (BitVec.toInt doubled)) 32)
    (R_set d __tup_0)
    (pure __tup_1) ) : SailM Bool )
  if ((sat1 || sat2) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QDSUB_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let doubled ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let sat1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let (doubled, sat1) ← (( do
    let (tup__0, tup__1) ← do (SignedSatQ (2 *i (BitVec.toInt (← (R_read n)))) 32)
    let doubled : (BitVec 32) := tup__0
    let sat1 : Bool := tup__1
    (pure (doubled, sat1)) ) : SailM ((BitVec 32) × Bool) )
  let sat2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let sat2 ← (( do
    let (__tup_0, __tup_1) ← do (SignedSatQ ((BitVec.toInt (← (R_read m))) -i (BitVec.toInt doubled)) 32)
    (R_set d __tup_0)
    (pure __tup_1) ) : SailM Bool )
  if ((sat1 || sat2) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QSAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let diff ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (← (SignedSat sum 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (← (SignedSat diff 16))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QSUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let diff2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (← (SignedSat diff1 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (← (SignedSat diff2 16))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QSUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let diff2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let diff3 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let diff4 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (← (SignedSat diff1 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (← (SignedSat diff2 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (← (SignedSat diff3 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (← (SignedSat diff4 8))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QSUB_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let sat ← (( do
    let (__tup_0, __tup_1) ← do (SignedSatQ ((BitVec.toInt (← (R_read m))) -i (BitVec.toInt (← (R_read n)))) 32)
    (R_set d __tup_0)
    (pure __tup_1) ) : SailM Bool )
  if (sat : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RBIT_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let result ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 31
    let mut loop_vars := result
    for i in [loop_i_lower:loop_i_upper:1]i do
      let result := loop_vars
      loop_vars ← do (pure (BitVec.update result (31 -i i) (Bit (BitVec.join1 [(BitVec.access (← (R_read m)) i)]))))
    (pure loop_vars) ) : SailM (BitVec 32) )
  (R_set d result)

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_REV16_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let result ← (pure (Sail.BitVec.updateSubrange result 31 24 (Sail.BitVec.extractLsb (← (R_read m)) 23 16)))
  let result ← (pure (Sail.BitVec.updateSubrange result 23 16 (Sail.BitVec.extractLsb (← (R_read m)) 31 24)))
  let result ← (pure (Sail.BitVec.updateSubrange result 15 8 (Sail.BitVec.extractLsb (← (R_read m)) 7 0)))
  let result ← (pure (Sail.BitVec.updateSubrange result 7 0 (Sail.BitVec.extractLsb (← (R_read m)) 15 8)))
  (R_set d result)

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_REV_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let result ← (pure (Sail.BitVec.updateSubrange result 31 24 (Sail.BitVec.extractLsb (← (R_read m)) 7 0)))
  let result ← (pure (Sail.BitVec.updateSubrange result 23 16 (Sail.BitVec.extractLsb (← (R_read m)) 15 8)))
  let result ← (pure (Sail.BitVec.updateSubrange result 15 8 (Sail.BitVec.extractLsb (← (R_read m)) 23 16)))
  let result ← (pure (Sail.BitVec.updateSubrange result 7 0 (Sail.BitVec.extractLsb (← (R_read m)) 31 24)))
  (R_set d result)

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_REVSH_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let result ← (pure (Sail.BitVec.updateSubrange result 31 8 (sign_extend (Sail.BitVec.extractLsb (← (R_read m)) 7 0) 24)))
  let result ← (pure (Sail.BitVec.updateSubrange result 7 0 (Sail.BitVec.extractLsb (← (R_read m)) 15 8)))
  (R_set d result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_ROR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0)))
  let (carry, result) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read n)) SRType_ROR shift_n (← readReg PSTATE).C)
    let result : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, result)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
      writeReg PSTATE { (← readReg PSTATE) with C := carry })
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSB_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (Complement.complement (← (R_read n))) imm32 1#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSB_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (Complement.complement (← (R_read n))) shifted 1#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSB_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (Complement.complement (← (R_read n))) shifted 1#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSC_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (Complement.complement (← (R_read n))) imm32 (← readReg PSTATE).C))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSC_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (Complement.complement (← (R_read n))) shifted (← readReg PSTATE).C))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSC_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (Complement.complement (← (R_read n))) shifted (← readReg PSTATE).C))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let sum2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange sum1 15 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange sum2 15 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 1 0
        (if ((sum1 ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 3 2
        (if ((sum2 ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let sum2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let sum3 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let sum4 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (integer_subrange sum1 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (integer_subrange sum2 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (integer_subrange sum3 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (integer_subrange sum4 7 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 0
        (Bit
          (if ((sum1 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 1
        (Bit
          (if ((sum2 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 2
        (Bit
          (if ((sum3 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 3
        (Bit
          (if ((sum4 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let sum ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange diff 15 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange sum 15 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 1 0
        (if ((diff ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 3 2
        (if ((sum ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }

def execute_aarch32_instrs_SB_Op_A_txt (_ : Unit) : SailM Unit := do
  (SpeculationBarrier ())

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SBC_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) (Complement.complement imm32) (← readReg PSTATE).C))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SBC_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) (Complement.complement shifted) (← readReg PSTATE).C))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SBC_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) (Complement.complement shifted) (← readReg PSTATE).C))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: d : Nat, lsbit : Nat, msbit : Int, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ lsbit ∧ lsbit ≤ 31 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SBFX_Op_A_txt (d : Nat) (lsbit : Nat) (msbit : Int) (n : Nat) : SailM Unit := do
  sail_assert ((lsbit ≤b msbit) && (msbit <b 32)) "src/instrs32.sail:11111.55-11111.56"
  (R_set d (sign_extend (Sail.BitVec.extractLsb (← (R_read n)) msbit lsbit) 32))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SDIV_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do
    if (((BitVec.toInt (← (R_read m))) == 0) : Bool)
    then (pure 0)
    else (do (pure (RoundTowardsZero (div_real (to_real (BitVec.toInt (← (R_read n)))) (to_real (BitVec.toInt (← (R_read m)))))))) ) : SailM Int )
  let result := result
  (R_set d (integer_subrange result 31 0))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SEL_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (R_set d
    (Sail.BitVec.updateSubrange (← (R_read d)) 7 0
      (← (do
        if (((BitVec.join1 [(BitVec.access (← readReg PSTATE).GE 0)]) == 1#1) : Bool)
        then (pure (Sail.BitVec.extractLsb (← (R_read n)) 7 0))
        else (pure (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))))
  (R_set d
    (Sail.BitVec.updateSubrange (← (R_read d)) 15 8
      (← (do
        if (((BitVec.join1 [(BitVec.access (← readReg PSTATE).GE 1)]) == 1#1) : Bool)
        then (pure (Sail.BitVec.extractLsb (← (R_read n)) 15 8))
        else (pure (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))))
  (R_set d
    (Sail.BitVec.updateSubrange (← (R_read d)) 23 16
      (← (do
        if (((BitVec.join1 [(BitVec.access (← readReg PSTATE).GE 2)]) == 1#1) : Bool)
        then (pure (Sail.BitVec.extractLsb (← (R_read n)) 23 16))
        else (pure (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))))
  (R_set d
    (Sail.BitVec.updateSubrange (← (R_read d)) 31 24
      (← (do
        if (((BitVec.join1 [(BitVec.access (← readReg PSTATE).GE 3)]) == 1#1) : Bool)
        then (pure (Sail.BitVec.extractLsb (← (R_read n)) 31 24))
        else (pure (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))))

/-- Type quantifiers: k_set_bigend : Bool -/
def execute_aarch32_instrs_SETEND_Op_A_txt (set_bigend : Bool) : SailM Unit := do
  (AArch32_CheckSETENDEnabled ())
  writeReg PSTATE { (← readReg PSTATE) with E := 
    if (set_bigend : Bool)
    then 1#1
    else 0#1 }

def execute_aarch32_instrs_SEV_Op_A_txt (_ : Unit) : Unit :=
  (SendEvent ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let sum2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange sum1 16 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange sum2 16 1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let sum2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let sum3 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let sum4 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (integer_subrange sum1 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (integer_subrange sum2 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (integer_subrange sum3 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (integer_subrange sum4 8 1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let sum ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange diff 16 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange sum 16 1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHSAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let diff ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange sum 16 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange diff 16 1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHSUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let diff2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange diff1 16 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange diff2 16 1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHSUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let diff2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let diff3 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let diff4 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (integer_subrange diff1 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (integer_subrange diff2 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (integer_subrange diff3 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (integer_subrange diff4 8 1)))

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, k_m_high : Bool, n : Nat, k_n_high : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMLABB_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (m_high : Bool) (n : Nat) (n_high : Bool) : SailM Unit := do
  let operand1 ← (( do
    if (n_high : Bool)
    then (pure (Sail.BitVec.extractLsb (← (R_read n)) 31 16))
    else (pure (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) ) : SailM (BitVec 16) )
  let operand2 ← (( do
    if (m_high : Bool)
    then (pure (Sail.BitVec.extractLsb (← (R_read m)) 31 16))
    else (pure (Sail.BitVec.extractLsb (← (R_read m)) 15 0)) ) : SailM (BitVec 16) )
  let result ← do (pure (((BitVec.toInt operand1) *i (BitVec.toInt operand2)) +i (BitVec.toInt (← (R_read a)))))
  (R_set d (integer_subrange result 31 0))
  if ((result != (BitVec.toInt (integer_subrange result 31 0))) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMLAD_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then (pure (ROR (← (R_read m)) 16))
    else (R_read m) ) : SailM (BitVec 32) )
  let product1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 15 0))))
  let product2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 31 16))))
  let result ← do (pure ((product1 +i product2) +i (BitVec.toInt (← (R_read a)))))
  (R_set d (integer_subrange result 31 0))
  if ((result != (BitVec.toInt (integer_subrange result 31 0))) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_SMLAL_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let result ← do (pure (((BitVec.toInt (← (R_read n))) *i (BitVec.toInt (← (R_read m)))) +i (BitVec.toInt ((← (R_read dHi)) +++ (← (R_read dLo))))))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(integer_access result 63)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit (integer_subrange result 63 0)) })
  else (pure ())

/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, k_m_high : Bool, n : Nat, k_n_high : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_SMLALBB_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (m_high : Bool) (n : Nat) (n_high : Bool) : SailM Unit := do
  let operand1 ← (( do
    if (n_high : Bool)
    then (pure (Sail.BitVec.extractLsb (← (R_read n)) 31 16))
    else (pure (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) ) : SailM (BitVec 16) )
  let operand2 ← (( do
    if (m_high : Bool)
    then (pure (Sail.BitVec.extractLsb (← (R_read m)) 31 16))
    else (pure (Sail.BitVec.extractLsb (← (R_read m)) 15 0)) ) : SailM (BitVec 16) )
  let result ← do (pure (((BitVec.toInt operand1) *i (BitVec.toInt operand2)) +i (BitVec.toInt ((← (R_read dHi)) +++ (← (R_read dLo))))))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))

/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_SMLALD_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then (pure (ROR (← (R_read m)) 16))
    else (R_read m) ) : SailM (BitVec 32) )
  let product1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 15 0))))
  let product2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 31 16))))
  let result ← do (pure ((product1 +i product2) +i (BitVec.toInt ((← (R_read dHi)) +++ (← (R_read dLo))))))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, k_m_high : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMLAWB_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (m_high : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_high : Bool)
    then (pure (Sail.BitVec.extractLsb (← (R_read m)) 31 16))
    else (pure (Sail.BitVec.extractLsb (← (R_read m)) 15 0)) ) : SailM (BitVec 16) )
  let result ← do (pure (((BitVec.toInt (← (R_read n))) *i (BitVec.toInt operand2)) +i (Int.shiftl (BitVec.toInt (← (R_read a))) 16)))
  (R_set d (integer_subrange result 47 16))
  if (((Int.shiftr result 16) != (BitVec.toInt (← (R_read d)))) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMLSD_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then (pure (ROR (← (R_read m)) 16))
    else (R_read m) ) : SailM (BitVec 32) )
  let product1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 15 0))))
  let product2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 31 16))))
  let result ← do (pure ((product1 -i product2) +i (BitVec.toInt (← (R_read a)))))
  (R_set d (integer_subrange result 31 0))
  if ((result != (BitVec.toInt (integer_subrange result 31 0))) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_SMLSLD_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then (pure (ROR (← (R_read m)) 16))
    else (R_read m) ) : SailM (BitVec 32) )
  let product1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 15 0))))
  let product2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 31 16))))
  let result ← do (pure ((product1 -i product2) +i (BitVec.toInt ((← (R_read dHi)) +++ (← (R_read dLo))))))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, k_round : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMMLA_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (n : Nat) (round : Bool) : SailM Unit := do
  let result ← (( do (pure ((Int.shiftl (BitVec.toInt (← (R_read a))) 32) +i ((BitVec.toInt (← (R_read n))) *i (BitVec.toInt (← (R_read m)))))) ) : SailM Int )
  let result : Int :=
    if (round : Bool)
    then (result +i (BitVec.toNat 0x80000000#32))
    else result
  let result := result
  (R_set d (integer_subrange result 63 32))

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, k_round : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMMLS_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (n : Nat) (round : Bool) : SailM Unit := do
  let result ← (( do (pure ((Int.shiftl (BitVec.toInt (← (R_read a))) 32) -i ((BitVec.toInt (← (R_read n))) *i (BitVec.toInt (← (R_read m)))))) ) : SailM Int )
  let result : Int :=
    if (round : Bool)
    then (result +i (BitVec.toNat 0x80000000#32))
    else result
  let result := result
  (R_set d (integer_subrange result 63 32))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_round : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SMMUL_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (round : Bool) : SailM Unit := do
  let result ← (( do (pure ((BitVec.toInt (← (R_read n))) *i (BitVec.toInt (← (R_read m))))) ) : SailM Int )
  let result : Int :=
    if (round : Bool)
    then (result +i (BitVec.toNat 0x80000000#32))
    else result
  let result := result
  (R_set d (integer_subrange result 63 32))

/-- Type quantifiers: d : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SMUAD_Op_A_txt (d : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then (pure (ROR (← (R_read m)) 16))
    else (R_read m) ) : SailM (BitVec 32) )
  let product1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 15 0))))
  let product2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 31 16))))
  let result := (product1 +i product2)
  (R_set d (integer_subrange result 31 0))
  if ((result != (BitVec.toInt (integer_subrange result 31 0))) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, k_m_high : Bool, n : Nat, k_n_high : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SMULBB_Op_A_txt (d : Nat) (m : Nat) (m_high : Bool) (n : Nat) (n_high : Bool) : SailM Unit := do
  let operand1 ← (( do
    if (n_high : Bool)
    then (pure (Sail.BitVec.extractLsb (← (R_read n)) 31 16))
    else (pure (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) ) : SailM (BitVec 16) )
  let operand2 ← (( do
    if (m_high : Bool)
    then (pure (Sail.BitVec.extractLsb (← (R_read m)) 31 16))
    else (pure (Sail.BitVec.extractLsb (← (R_read m)) 15 0)) ) : SailM (BitVec 16) )
  let result := ((BitVec.toInt operand1) *i (BitVec.toInt operand2))
  (R_set d (integer_subrange result 31 0))

/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_SMULL_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let result ← do (pure ((BitVec.toInt (← (R_read n))) *i (BitVec.toInt (← (R_read m)))))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(integer_access result 63)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit (integer_subrange result 63 0)) })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, k_m_high : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SMULWB_Op_A_txt (d : Nat) (m : Nat) (m_high : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_high : Bool)
    then (pure (Sail.BitVec.extractLsb (← (R_read m)) 31 16))
    else (pure (Sail.BitVec.extractLsb (← (R_read m)) 15 0)) ) : SailM (BitVec 16) )
  let product ← do (pure ((BitVec.toInt (← (R_read n))) *i (BitVec.toInt operand2)))
  (R_set d (integer_subrange product 47 16))

/-- Type quantifiers: d : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SMUSD_Op_A_txt (d : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then (pure (ROR (← (R_read m)) 16))
    else (R_read m) ) : SailM (BitVec 32) )
  let product1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 15 0))))
  let product2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) *i (BitVec.toInt (Sail.BitVec.extractLsb operand2 31 16))))
  let result := (product1 -i product2)
  (R_set d (integer_subrange result 31 0))

/-- Type quantifiers: d : Nat, n : Nat, saturate_to : Nat, 1 ≤ saturate_to ∧ saturate_to ≤ 16 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SSAT16_Op_A_txt (d : Nat) (n : Nat) (saturate_to : Nat) : SailM Unit := do
  let result1 ← (( do (undefined_bitvector saturate_to) ) : SailM (BitVec saturate_to) )
  let result2 ← (( do (undefined_bitvector saturate_to) ) : SailM (BitVec saturate_to) )
  let sat1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let sat2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let (result1, sat1) ← (( do
    let (tup__0, tup__1) ← do (SignedSatQ (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) saturate_to)
    let result1 : (BitVec saturate_to) := tup__0
    let sat1 : Bool := tup__1
    (pure (result1, sat1)) ) : SailM ((BitVec saturate_to) × Bool) )
  let (result2, sat2) ← (( do
    let (tup__0, tup__1) ← do (SignedSatQ (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) saturate_to)
    let result2 : (BitVec saturate_to) := tup__0
    let sat2 : Bool := tup__1
    (pure (result2, sat2)) ) : SailM ((BitVec saturate_to) × Bool) )
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (sign_extend result1 16)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (sign_extend result2 16)))
  if ((sat1 || sat2) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, saturate_to : Nat, shift_n : Int, 1 ≤ saturate_to ∧ saturate_to ≤ 32 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SSAT_Op_A_txt (d : Nat) (n : Nat) (saturate_to : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let result ← (( do (undefined_bitvector saturate_to) ) : SailM (BitVec saturate_to) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let operand ← (( do (Shift (← (R_read n)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (result, sat) ← (( do
    let (tup__0, tup__1) ← do (SignedSatQ (BitVec.toInt operand) saturate_to)
    let result : (BitVec saturate_to) := tup__0
    let sat : Bool := tup__1
    (pure (result, sat)) ) : SailM ((BitVec saturate_to) × Bool) )
  (R_set d (sign_extend result 32))
  if (sat : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SSAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let diff ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange sum 15 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange diff 15 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 1 0
        (if ((sum ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 3 2
        (if ((diff ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SSUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let diff2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange diff1 15 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange diff2 15 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 1 0
        (if ((diff1 ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 3 2
        (if ((diff2 ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SSUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let diff2 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let diff3 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let diff4 ← do (pure ((BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) -i (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (integer_subrange diff1 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (integer_subrange diff2 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (integer_subrange diff3 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (integer_subrange diff4 7 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 0
        (Bit
          (if ((diff1 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 1
        (Bit
          (if ((diff2 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 2
        (Bit
          (if ((diff3 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 3
        (Bit
          (if ((diff4 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }

/-- Type quantifiers: k_add : Bool, cp : Nat, k_index : Bool, n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ cp = 14 -/
def execute_aarch32_instrs_STC_Op_A_txt (add : Bool) (cp : Nat) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SysRegRead cp (← (ThisInstr ())) (Sail.BitVec.extractLsb address 31 0))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STM_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 14
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
        then
          (do
            if ((((i == n) && wback) && (i != (LowestSetBit registers))) : Bool)
            then (MemS_set address 4 (← (__UNKNOWN_bits 32)))
            else (MemS_set address 4 (← (R_read i)))
            (pure (BitVec.addInt address 4)))
        else (pure address)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
  then (MemS_set address 4 (← (PCStoreValue ())))
  else (pure ())
  if (wback : Bool)
  then (R_set n (BitVec.addInt (← (R_read n)) (4 *i (BitCount registers))))
  else (pure ())

/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STMDA_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let address ← (( do (pure (BitVec.addInt (BitVec.subInt (← (R_read n)) (4 *i (BitCount registers))) 4)) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 14
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
        then
          (do
            if ((((i == n) && wback) && (i != (LowestSetBit registers))) : Bool)
            then (MemS_set address 4 (← (__UNKNOWN_bits 32)))
            else (MemS_set address 4 (← (R_read i)))
            (pure (BitVec.addInt address 4)))
        else (pure address)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
  then (MemS_set address 4 (← (PCStoreValue ())))
  else (pure ())
  if (wback : Bool)
  then (R_set n (BitVec.subInt (← (R_read n)) (4 *i (BitCount registers))))
  else (pure ())

/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STMDB_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let address ← (( do (pure (BitVec.subInt (← (R_read n)) (4 *i (BitCount registers)))) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 14
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
        then
          (do
            if ((((i == n) && wback) && (i != (LowestSetBit registers))) : Bool)
            then (MemS_set address 4 (← (__UNKNOWN_bits 32)))
            else (MemS_set address 4 (← (R_read i)))
            (pure (BitVec.addInt address 4)))
        else (pure address)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
  then (MemS_set address 4 (← (PCStoreValue ())))
  else (pure ())
  if (wback : Bool)
  then (R_set n (BitVec.subInt (← (R_read n)) (4 *i (BitCount registers))))
  else (pure ())

/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STMIB_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let address ← (( do (pure (BitVec.addInt (← (R_read n)) 4)) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 14
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
        then
          (do
            if ((((i == n) && wback) && (i != (LowestSetBit registers))) : Bool)
            then (MemS_set address 4 (← (__UNKNOWN_bits 32)))
            else (MemS_set address 4 (← (R_read i)))
            (pure (BitVec.addInt address 4)))
        else (pure address)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
  then (MemS_set address 4 (← (PCStoreValue ())))
  else (pure ())
  if (wback : Bool)
  then (R_set n (BitVec.addInt (← (R_read n)) (4 *i (BitCount registers))))
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRB_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  (MemU_set address 1 (Sail.BitVec.extractLsb (← (R_read t)) 7 0))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRB_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  (MemU_set address 1 (Sail.BitVec.extractLsb (← (R_read t)) 7 0))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_STRB_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  (MemU_set address 1 (Sail.BitVec.extractLsb (← (R_read t)) 7 0))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, shift_n : Int, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRBT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (shift_n : Int) (shift_t : SRType) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let offset ← (( do
    if (register_form : Bool)
    then (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    else (pure imm32) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then (R_read n)
    else (pure offset_addr) ) : SailM (BitVec 32) )
  if ((←((pure ((! postindex) && (t != 15))) <&&> (do
       (pure ((← readReg PSTATE).T == 1#1))))) : Bool)
  then (pure (AArch32_SetLSInstructionSyndrome 1 false t false))
  else (pure ())
  (MemU_unpriv_set address 1 (Sail.BitVec.extractLsb (← (R_read t)) 7 0))
  if (postindex : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, t2 : Nat, k_wback : Bool, 0 ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRD_i_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (t2 : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  if ((IsAligned__1 address 8) : Bool)
  then
    (do
      let data ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
      let data ← (( do
        if ((← (BigEndian AccessType_GPR)) : Bool)
        then
          (do
            let data ← (pure (Sail.BitVec.updateSubrange data 63 32 (← (R_read t))))
            (pure (Sail.BitVec.updateSubrange data 31 0 (← (R_read t2)))))
        else
          (do
            let data ← (pure (Sail.BitVec.updateSubrange data 31 0 (← (R_read t))))
            (pure (Sail.BitVec.updateSubrange data 63 32 (← (R_read t2))))) ) : SailM (BitVec 64) )
      (MemA_set address 8 data))
  else
    (do
      (MemA_set address 4 (← (R_read t)))
      (MemA_set (BitVec.addInt address 4) 4 (← (R_read t2))))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, t : Nat, t2 : Nat, k_wback : Bool, 1 ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_STRD_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (t : Nat) (t2 : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + (← (R_read m))))
    else (pure ((← (R_read n)) - (← (R_read m)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  if ((IsAligned__1 address 8) : Bool)
  then
    (do
      let data ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
      let data ← (( do
        if ((← (BigEndian AccessType_GPR)) : Bool)
        then
          (do
            let data ← (pure (Sail.BitVec.updateSubrange data 63 32 (← (R_read t))))
            (pure (Sail.BitVec.updateSubrange data 31 0 (← (R_read t2)))))
        else
          (do
            let data ← (pure (Sail.BitVec.updateSubrange data 31 0 (← (R_read t))))
            (pure (Sail.BitVec.updateSubrange data 63 32 (← (R_read t2))))) ) : SailM (BitVec 64) )
      (MemA_set address 8 data))
  else
    (do
      (MemA_set address 4 (← (R_read t)))
      (MemA_set (BitVec.addInt address 4) 4 (← (R_read t2))))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STREX_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (pure ((← (R_read n)) + imm32)) ) : SailM (BitVec 32) )
  if ((← (AArch32_ExclusiveMonitorsPass address 4)) : Bool)
  then
    (do
      (MemA_set address 4 (← (R_read t)))
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else (R_set d (Sail.BitVec.zeroExtend 1#1 32))

/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STREXB_Op_A_txt (d : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  if ((← (AArch32_ExclusiveMonitorsPass address 1)) : Bool)
  then
    (do
      (MemA_set address 1 (Sail.BitVec.extractLsb (← (R_read t)) 7 0))
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else (R_set d (Sail.BitVec.zeroExtend 1#1 32))

/-- Type quantifiers: d : Nat, n : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STREXD_Op_A_txt (d : Nat) (n : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let value_name ← (( do
    if ((← (BigEndian AccessType_GPR)) : Bool)
    then (pure ((← (R_read t)) +++ (← (R_read t2))))
    else (pure ((← (R_read t2)) +++ (← (R_read t)))) ) : SailM (BitVec 64) )
  if ((← (AArch32_ExclusiveMonitorsPass address 8)) : Bool)
  then
    (do
      (MemA_set address 8 value_name)
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else (R_set d (Sail.BitVec.zeroExtend 1#1 32))

/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STREXH_Op_A_txt (d : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  if ((← (AArch32_ExclusiveMonitorsPass address 2)) : Bool)
  then
    (do
      (MemA_set address 2 (Sail.BitVec.extractLsb (← (R_read t)) 15 0))
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else (R_set d (Sail.BitVec.zeroExtend 1#1 32))

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRH_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  (MemU_set address 2 (Sail.BitVec.extractLsb (← (R_read t)) 15 0))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRH_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  (MemU_set address 2 (Sail.BitVec.extractLsb (← (R_read t)) 15 0))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_STRH_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  (MemU_set address 2 (Sail.BitVec.extractLsb (← (R_read t)) 15 0))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRHT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let offset ← (( do
    if (register_form : Bool)
    then (R_read m)
    else (pure imm32) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then (R_read n)
    else (pure offset_addr) ) : SailM (BitVec 32) )
  if ((←((pure (t != 15)) <&&> (do
       (pure ((← readReg PSTATE).T == 1#1))))) : Bool)
  then (pure (AArch32_SetLSInstructionSyndrome 2 false t false))
  else (pure ())
  (MemU_unpriv_set address 2 (Sail.BitVec.extractLsb (← (R_read t)) 15 0))
  if (postindex : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STR_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  (MemU_set address 4
    (← (do
      if ((t == 15) : Bool)
      then (PCStoreValue ())
      else (R_read t))))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STR_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  (MemU_set address 4 (← (R_read t)))
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_STR_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure offset_addr)
    else (R_read n) ) : SailM (BitVec 32) )
  let data ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let data ← (( do
    if ((t == 15) : Bool)
    then (do (PCStoreValue ()))
    else (do (R_read t)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  (MemU_set address 4 data)
  if (wback : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, shift_n : Int, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (shift_n : Int) (shift_t : SRType) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let offset ← (( do
    if (register_form : Bool)
    then (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    else (pure imm32) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + offset))
    else (pure ((← (R_read n)) - offset)) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then (R_read n)
    else (pure offset_addr) ) : SailM (BitVec 32) )
  let data ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let data ← (( do
    if ((t == 15) : Bool)
    then (do (PCStoreValue ()))
    else (do (R_read t)) ) : SailM (BitVec 32) )
  if ((←((pure ((! postindex) && (t != 15))) <&&> (do
       (pure ((← readReg PSTATE).T == 1#1))))) : Bool)
  then (pure (AArch32_SetLSInstructionSyndrome 4 false t false))
  else (pure ())
  (MemU_unpriv_set address 4 data)
  if (postindex : Bool)
  then (R_set n offset_addr)
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SUB_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) (Complement.complement imm32) 1#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SUB_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) (Complement.complement shifted) 1#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SUB_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read n)) (Complement.complement shifted) 1#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: d : Nat, k_setflags : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SUB_SP_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read 13)) (Complement.complement imm32) 1#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SUB_SP_r_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shifted ← (( do (Shift (← (R_read m)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry (← (R_read 13)) (Complement.complement shifted) 1#1))
    let result : (BitVec 32) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec 32)) )
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then (ALUExceptionReturn result)
      else (ALUWritePC result))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure ()))

def execute_aarch32_instrs_SVC_Op_A_txt (imm32 : (BitVec 32)) : SailM Unit := do
  (AArch32_CheckForSVCTrap (Sail.BitVec.extractLsb imm32 15 0))
  (AArch32_CallSupervisor (Sail.BitVec.extractLsb imm32 15 0))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTAB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 ((Sail.BitVec.extractLsb (← (R_read n)) 15 0) + (sign_extend (Sail.BitVec.extractLsb rotated 7 0) 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 ((Sail.BitVec.extractLsb (← (R_read n)) 31 16) + (sign_extend (Sail.BitVec.extractLsb rotated 23 16) 16))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTAB_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d ((← (R_read n)) + (sign_extend (Sail.BitVec.extractLsb rotated 7 0) 32)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTAH_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d ((← (R_read n)) + (sign_extend (Sail.BitVec.extractLsb rotated 15 0) 32)))

/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTB16_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (sign_extend (Sail.BitVec.extractLsb rotated 7 0) 16)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (sign_extend (Sail.BitVec.extractLsb rotated 23 16) 16)))

/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTB_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d (sign_extend (Sail.BitVec.extractLsb rotated 7 0) 32))

/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTH_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d (sign_extend (Sail.BitVec.extractLsb rotated 15 0) 32))

/-- Type quantifiers: k_is_tbh : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_TBB_Op_A_txt (is_tbh : Bool) (m : Nat) (n : Nat) : SailM Unit := do
  let halfwords ← (( do (undefined_range 0 65535) ) : SailM Nat )
  let halfwords ← (( do
    if (is_tbh : Bool)
    then (do (pure (BitVec.toNat (← (MemU_read ((← (R_read n)) + ((← (R_read m)) <<< 1)) 2)))))
    else (do (pure (BitVec.toNat (← (MemU_read ((← (R_read n)) + (← (R_read m))) 1))))) ) : SailM Nat )
  let halfwords := halfwords
  (BranchWritePC (BitVec.addInt (← (PC_read__1 ())) (2 *i halfwords)) BranchType_INDIR)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_TEQ_i_Op_A_txt (carry : (BitVec 1)) (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let result ← (( do (pure ((← (R_read n)) ^^^ imm32)) ) : SailM (BitVec 32) )
  writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
  writeReg PSTATE { (← readReg PSTATE) with C := carry }

/-- Type quantifiers: m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_TEQ_r_Op_A_txt (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) ^^^ shifted)) ) : SailM (BitVec 32) )
  writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
  writeReg PSTATE { (← readReg PSTATE) with C := carry }

/-- Type quantifiers: m : Nat, n : Nat, s : Nat, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_TEQ_rr_Op_A_txt (m : Nat) (n : Nat) (s : Nat) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) ^^^ shifted)) ) : SailM (BitVec 32) )
  writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
  writeReg PSTATE { (← readReg PSTATE) with C := carry }

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_TST_i_Op_A_txt (carry : (BitVec 1)) (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let result ← (( do (pure ((← (R_read n)) &&& imm32)) ) : SailM (BitVec 32) )
  writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
  writeReg PSTATE { (← readReg PSTATE) with C := carry }

/-- Type quantifiers: m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_TST_r_Op_A_txt (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) &&& shifted)) ) : SailM (BitVec 32) )
  writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
  writeReg PSTATE { (← readReg PSTATE) with C := carry }

/-- Type quantifiers: m : Nat, n : Nat, s : Nat, 0 ≤ s ∧ s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_TST_rr_Op_A_txt (m : Nat) (n : Nat) (s : Nat) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let shift_n ← do (pure (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read s)) 7 0)))
  let (carry, shifted) ← (( do
    let (tup__0, tup__1) ← do (Shift_C (← (R_read m)) shift_t shift_n (← readReg PSTATE).C)
    let shifted : (BitVec 32) := tup__0
    let carry : (BitVec 1) := tup__1
    (pure (carry, shifted)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  let result ← (( do (pure ((← (R_read n)) &&& shifted)) ) : SailM (BitVec 32) )
  writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access result 31)]) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit result) }
  writeReg PSTATE { (← readReg PSTATE) with C := carry }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let sum2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange sum1 15 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange sum2 15 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 1 0
        (if ((sum1 ≥b (BitVec.toNat 0x10000#20)) : Bool)
        then 0b11#2
        else 0b00#2)))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 3 2
        (if ((sum2 ≥b (BitVec.toNat 0x10000#20)) : Bool)
        then 0b11#2
        else 0b00#2)))) }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let sum2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let sum3 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let sum4 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (integer_subrange sum1 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (integer_subrange sum2 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (integer_subrange sum3 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (integer_subrange sum4 7 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 0
        (Bit
          (if ((sum1 ≥b (BitVec.toNat 0x100#12)) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 1
        (Bit
          (if ((sum2 ≥b (BitVec.toNat 0x100#12)) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 2
        (Bit
          (if ((sum3 ≥b (BitVec.toNat 0x100#12)) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 3
        (Bit
          (if ((sum4 ≥b (BitVec.toNat 0x100#12)) : Bool)
          then 1#1
          else 0#1))))) }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let sum ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange diff 15 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange sum 15 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 1 0
        (if ((diff ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 3 2
        (if ((sum ≥b (BitVec.toNat 0x10000#20)) : Bool)
        then 0b11#2
        else 0b00#2)))) }

/-- Type quantifiers: d : Nat, lsbit : Nat, msbit : Int, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ lsbit ∧ lsbit ≤ 31 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UBFX_Op_A_txt (d : Nat) (lsbit : Nat) (msbit : Int) (n : Nat) : SailM Unit := do
  sail_assert ((lsbit ≤b msbit) && (msbit <b 32)) "src/instrs32.sail:17195.55-17195.56"
  (R_set d (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb (← (R_read n)) msbit lsbit) 32))

def execute_aarch32_instrs_UDF_Op_A_txt (_ : Unit) : SailM Unit := do
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UDIV_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do
    if (((BitVec.toNat (← (R_read m))) == 0) : Bool)
    then (pure 0)
    else (do (pure (RoundTowardsZero (div_real (to_real (BitVec.toNat (← (R_read n)))) (to_real (BitVec.toNat (← (R_read m)))))))) ) : SailM Int )
  let result := result
  (R_set d (integer_subrange result 31 0))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let sum2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange sum1 16 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange sum2 16 1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let sum2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let sum3 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let sum4 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (integer_subrange sum1 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (integer_subrange sum2 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (integer_subrange sum3 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (integer_subrange sum4 8 1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let sum ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange diff 16 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange sum 16 1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHSAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let diff ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange sum 16 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange diff 16 1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHSUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let diff2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange diff1 16 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange diff2 16 1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHSUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let diff2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let diff3 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let diff4 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (integer_subrange diff1 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (integer_subrange diff2 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (integer_subrange diff3 8 1)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (integer_subrange diff4 8 1)))

/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_UMAAL_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let result ← do (pure ((((BitVec.toNat (← (R_read n))) *i (BitVec.toNat (← (R_read m)))) +i (BitVec.toNat (← (R_read dHi)))) +i (BitVec.toNat (← (R_read dLo)))))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))

/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_UMLAL_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let result ← do (pure (((BitVec.toNat (← (R_read n))) *i (BitVec.toNat (← (R_read m)))) +i (BitVec.toNat ((← (R_read dHi)) +++ (← (R_read dLo))))))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(integer_access result 63)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit (integer_subrange result 63 0)) })
  else (pure ())

/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_UMULL_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let result ← do (pure ((BitVec.toNat (← (R_read n))) *i (BitVec.toNat (← (R_read m)))))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(integer_access result 63)]) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (IsZeroBit (integer_subrange result 63 0)) })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let sum2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (← (UnsignedSat sum1 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (← (UnsignedSat sum2 16))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let sum2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let sum3 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let sum4 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (← (UnsignedSat sum1 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (← (UnsignedSat sum2 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (← (UnsignedSat sum3 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (← (UnsignedSat sum4 8))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let sum ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (← (UnsignedSat diff 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (← (UnsignedSat sum 16))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQSAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let diff ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (← (UnsignedSat sum 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (← (UnsignedSat diff 16))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQSUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let diff2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (← (UnsignedSat diff1 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (← (UnsignedSat diff2 16))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQSUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let diff2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let diff3 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let diff4 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (← (UnsignedSat diff1 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (← (UnsignedSat diff2 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (← (UnsignedSat diff3 8))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (← (UnsignedSat diff4 8))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USAD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let absdiff1 ← do (pure (Int.natAbs ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0)))))
  let absdiff2 ← do (pure (Int.natAbs ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 8)))))
  let absdiff3 ← do (pure (Int.natAbs ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 23 16)))))
  let absdiff4 ← do (pure (Int.natAbs ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 24)))))
  let result := (((absdiff1 +i absdiff2) +i absdiff3) +i absdiff4)
  (R_set d (integer_subrange result 31 0))

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_USADA8_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let absdiff1 ← do (pure (Int.natAbs ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0)))))
  let absdiff2 ← do (pure (Int.natAbs ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 8)))))
  let absdiff3 ← do (pure (Int.natAbs ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 23 16)))))
  let absdiff4 ← do (pure (Int.natAbs ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 24)))))
  let result ← do (pure (((((BitVec.toNat (← (R_read a))) +i absdiff1) +i absdiff2) +i absdiff3) +i absdiff4))
  (R_set d (integer_subrange result 31 0))

/-- Type quantifiers: d : Nat, n : Nat, saturate_to : Nat, 0 ≤ saturate_to ∧ saturate_to ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USAT16_Op_A_txt (d : Nat) (n : Nat) (saturate_to : Nat) : SailM Unit := do
  let result1 ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  let result2 ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  let sat1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let sat2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let (result1, sat1) ← (( do
    let (tup__0, tup__1) ← do (ZeroUnsignedSatQ (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) saturate_to 16)
    let result1 : (BitVec 16) := tup__0
    let sat1 : Bool := tup__1
    (pure (result1, sat1)) ) : SailM ((BitVec 16) × Bool) )
  let (result2, sat2) ← (( do
    let (tup__0, tup__1) ← do (ZeroUnsignedSatQ (BitVec.toInt (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) saturate_to 16)
    let result2 : (BitVec 16) := tup__0
    let sat2 : Bool := tup__1
    (pure (result2, sat2)) ) : SailM ((BitVec 16) × Bool) )
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 result1))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 result2))
  if ((sat1 || sat2) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, saturate_to : Nat, shift_n : Int, 0 ≤ saturate_to ∧ saturate_to ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USAT_Op_A_txt (d : Nat) (n : Nat) (saturate_to : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let result ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let operand ← (( do (Shift (← (R_read n)) shift_t shift_n (← readReg PSTATE).C) ) : SailM (BitVec 32) )
  let (result, sat) ← (( do
    let (tup__0, tup__1) ← do (ZeroUnsignedSatQ (BitVec.toInt operand) saturate_to 32)
    let result : (BitVec 32) := tup__0
    let sat : Bool := tup__1
    (pure (result, sat)) ) : SailM ((BitVec 32) × Bool) )
  (R_set d result)
  if (sat : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Q := 1#1 }
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sum ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) +i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  let diff ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange sum 15 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange diff 15 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 1 0
        (if ((sum ≥b (BitVec.toNat 0x10000#20)) : Bool)
        then 0b11#2
        else 0b00#2)))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 3 2
        (if ((diff ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 0))))
  let diff2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (integer_subrange diff1 15 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (integer_subrange diff2 15 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 1 0
        (if ((diff1 ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).GE 3 2
        (if ((diff2 ≥b 0) : Bool)
        then 0b11#2
        else 0b00#2)))) }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let diff1 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 7 0)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 7 0))))
  let diff2 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 15 8)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 15 8))))
  let diff3 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 23 16)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 23 16))))
  let diff4 ← do (pure ((BitVec.toNat (Sail.BitVec.extractLsb (← (R_read n)) 31 24)) -i (BitVec.toNat (Sail.BitVec.extractLsb (← (R_read m)) 31 24))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 7 0 (integer_subrange diff1 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 8 (integer_subrange diff2 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 23 16 (integer_subrange diff3 7 0)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 24 (integer_subrange diff4 7 0)))
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 0
        (Bit
          (if ((diff1 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 1
        (Bit
          (if ((diff2 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 2
        (Bit
          (if ((diff3 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }
  writeReg PSTATE { (← readReg PSTATE) with GE := ← (do 
    (pure (BitVec.update (← readReg PSTATE).GE 3
        (Bit
          (if ((diff4 ≥b 0) : Bool)
          then 1#1
          else 0#1))))) }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTAB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 ((Sail.BitVec.extractLsb (← (R_read n)) 15 0) + (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 7 0) 16))))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 ((Sail.BitVec.extractLsb (← (R_read n)) 31 16) + (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 23 16) 16))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTAB_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d ((← (R_read n)) + (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 7 0) 32)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTAH_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d ((← (R_read n)) + (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 15 0) 32)))

/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTB16_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 15 0 (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 7 0) 16)))
  (R_set d (Sail.BitVec.updateSubrange (← (R_read d)) 31 16 (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 23 16) 16)))

/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTB_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 7 0) 32))

/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧ rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTH_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let rotated ← (( do (pure (ROR (← (R_read m)) rotation)) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 15 0) 32))

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_long_destination : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VABA_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let absdiff ← (( do (undefined_int ()) ) : SailM Int )
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (absdiff, op1, op2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (absdiff, op1, op2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (absdiff, op1, op2) := loop_vars
      loop_vars ← do
        let (absdiff, op1, op2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (absdiff, op1, op2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (absdiff, op1, op2) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (Din_read (n +i r))) e esize)
              let op2 ← (Elem_read (← (Din_read (m +i r))) e esize)
              let absdiff ← (pure (Int.natAbs ((← (asl_Int op1 is_unsigned)) -i (← (asl_Int op2 is_unsigned)))))
              if (long_destination : Bool)
              then (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) (BitVec.addInt (← (Elem_read (← (Qin_read (Int.shiftr d 1))) e (2 *i esize))) absdiff))))
              else (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (BitVec.addInt (← (Elem_read (← (Din_read (d +i r))) e esize)) absdiff))))
              (pure (absdiff, op1, op2))
          (pure loop_vars_1) ) : SailM (Int × (BitVec esize) × (BitVec esize)) )
        (pure (absdiff, op1, op2))
    (pure loop_vars) ) : SailM (Int × (BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VABD_f_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, op2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2) := loop_vars
      loop_vars ← do
        let (op1, op2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (n +i r))) e esize)
              let op2 ← (Elem_read (← (D_read (m +i r))) e esize)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPAbs (← (FPSub op1 op2 (← (StandardFPSCRValue ())))))))))
              (pure (op1, op2))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, op2))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_long_destination : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VABD_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let absdiff ← (( do (undefined_int ()) ) : SailM Int )
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (absdiff, op1, op2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (absdiff, op1, op2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (absdiff, op1, op2) := loop_vars
      loop_vars ← do
        let (absdiff, op1, op2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (absdiff, op1, op2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (absdiff, op1, op2) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (Din_read (n +i r))) e esize)
              let op2 ← (Elem_read (← (Din_read (m +i r))) e esize)
              let absdiff ← (pure (Int.natAbs ((← (asl_Int op1 is_unsigned)) -i (← (asl_Int op2 is_unsigned)))))
              if (long_destination : Bool)
              then (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) (integer_subrange absdiff ((2 *i esize) -i 1) 0))))
              else (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange absdiff (esize -i 1) 0))))
              (pure (absdiff, op1, op2))
          (pure loop_vars_1) ) : SailM (Int × (BitVec esize) × (BitVec esize)) )
        (pure (absdiff, op1, op2))
    (pure loop_vars) ) : SailM (Int × (BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs : Int, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VABS_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let result ← (( do
        let loop_r_lower := 0
        let loop_r_upper := (regs -i 1)
        let mut loop_vars := result
        for r in [loop_r_lower:loop_r_upper:1]i do
          let result := loop_vars
          loop_vars ← do
            let loop_e_lower := 0
            let loop_e_upper := (elements -i 1)
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                if (floating_point : Bool)
                then
                  (do
                    sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs32.sail:19798.61-19798.62"
                    (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPAbs (← (Elem_read (← (D_read (m +i r))) e esize)))))))
                    (pure result))
                else
                  (do
                    let result ← (pure (Int.natAbs (BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize)))))
                    (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange result (esize -i 1) 0))))
                    (pure result))
            (pure loop_vars_1)
        (pure loop_vars) ) : SailM Int )
      (pure ()))
  else
    (do
      match esize with
      | 16 => (S_set d ((Zeros (n := 16)) +++ (← (FPAbs (Sail.BitVec.extractLsb (← (S_read m)) 15 0)))))
      | 32 => (S_set d (← (FPAbs (← (S_read m)))))
      | 64 => (D_set d (← (FPAbs (← (D_read m)))))
      | _ => (pure ()))

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, n : Nat, k_or_equal : Bool, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VACGE_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (n : Nat) (or_equal : Bool) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, op2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2) := loop_vars
      loop_vars ← do
        let (op1, op2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (FPAbs (← (Elem_read (← (D_read (n +i r))) e esize)))
              let op2 ← (FPAbs (← (Elem_read (← (D_read (m +i r))) e esize)))
              let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
              let test_passed ← (( do
                if (or_equal : Bool)
                then (do (FPCompareGE op1 op2 (← (StandardFPSCRValue ()))))
                else (do (FPCompareGT op1 op2 (← (StandardFPSCRValue ())))) ) : SailM Bool )
              (D_set (d +i r)
                (← (Elem_set (← (D_read (d +i r))) e esize
                    (if (test_passed : Bool)
                    then (Ones (n := esize))
                    else (Zeros (n := esize))))))
              (pure (op1, op2))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, op2))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VADD_f_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let loop_r_lower := 0
      let loop_r_upper := (regs -i 1)
      let mut loop_vars := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPAdd (← (Elem_read (← (D_read (n +i r))) e esize)) (← (Elem_read (← (D_read (m +i r))) e esize)) (← (StandardFPSCRValue ())))))))
          (pure loop_vars_1)
      (pure loop_vars))
  else
    (do
      match esize with
      | 16 => (S_set d ((Zeros (n := 16)) +++ (← (FPAdd (Sail.BitVec.extractLsb (← (S_read n)) 15 0) (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ()))))))
      | 32 => (S_set d (← (FPAdd (← (S_read n)) (← (S_read m)) (← (FPSCR_read ())))))
      | 64 => (D_set d (← (FPAdd (← (D_read n)) (← (D_read m)) (← (FPSCR_read ())))))
      | _ => (pure ()))

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VADDHN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (pure ((← (Elem_read (← (Qin_read (Int.shiftr n 1))) e (2 *i esize))) + (← (Elem_read (← (Qin_read (Int.shiftr m 1))) e (2 *i esize)))))
        (D_set d (← (Elem_set (← (D_read d)) e esize (Sail.BitVec.extractLsb result ((2 *i esize) -i 1) esize))))
        (pure result)
    (pure loop_vars) ) : SailM (BitVec (2 * esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VADD_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize ((← (Elem_read (← (D_read (n +i r))) e esize)) + (← (Elem_read (← (D_read (m +i r))) e esize))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_is_vaddw : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VADDL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (is_vaddw : Bool) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let op1 ← (( do (undefined_int ()) ) : SailM Int )
        let op1 ← (( do
          if (is_vaddw : Bool)
          then (do (asl_Int (← (Elem_read (← (Qin_read (Int.shiftr n 1))) e (2 *i esize))) is_unsigned))
          else (do (asl_Int (← (Elem_read (← (Din_read n)) e esize)) is_unsigned)) ) : SailM Int )
        let op1 := op1
        let result ← (pure (op1 +i (← (asl_Int (← (Elem_read (← (Din_read m)) e esize)) is_unsigned))))
        (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) (integer_subrange result ((2 *i esize) -i 1) 0))))
        (pure result)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VAND_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set (d +i r) ((← (D_read (n +i r))) &&& (← (D_read (m +i r)))))
  (pure loop_vars)

/-- Type quantifiers: d : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VBIC_i_Op_A_txt (d : Nat) (imm64 : (BitVec 64)) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set (d +i r) ((← (D_read (d +i r))) &&& (Complement.complement imm64)))
  (pure loop_vars)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VBIC_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set (d +i r) ((← (D_read (n +i r))) &&& (Complement.complement (← (D_read (m +i r))))))
  (pure loop_vars)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VBIF_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (operation : VBitOps) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      match operation with
      | .VBitOps_VBIF => (D_set (d +i r) (((← (D_read (d +i r))) &&& (← (D_read (m +i r)))) ||| ((← (D_read (n +i r))) &&& (Complement.complement (← (D_read (m +i r)))))))
      | .VBitOps_VBIT => (D_set (d +i r) (((← (D_read (n +i r))) &&& (← (D_read (m +i r)))) ||| ((← (D_read (d +i r))) &&& (Complement.complement (← (D_read (m +i r)))))))
      | .VBitOps_VBSL => (D_set (d +i r) (((← (D_read (n +i r))) &&& (← (D_read (d +i r)))) ||| ((← (D_read (m +i r))) &&& (Complement.complement (← (D_read (d +i r)))))))
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCEQ_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
          let test_passed ← (( do
            if (floating_point : Bool)
            then
              (do
                sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs32.sail:21029.57-21029.58"
                let zero ← (( do (FPZero 0#1 esize) ) : SailM (BitVec esize) )
                (FPCompareEQ (← (Elem_read (← (D_read (m +i r))) e esize)) zero (← (StandardFPSCRValue ()))))
            else (do (pure ((← (Elem_read (← (D_read (m +i r))) e esize)) == (Zeros (n := esize))))) ) : SailM Bool )
          (D_set (d +i r)
            (← (Elem_set (← (D_read (d +i r))) e esize
                (if (test_passed : Bool)
                then (Ones (n := esize))
                else (Zeros (n := esize))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_int_operation : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCEQ_r_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (int_operation : Bool) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, op2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2) := loop_vars
      loop_vars ← do
        let (op1, op2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (n +i r))) e esize)
              let op2 ← (Elem_read (← (D_read (m +i r))) e esize)
              let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
              let test_passed ← (( do
                if (int_operation : Bool)
                then (pure (op1 == op2))
                else
                  (do
                    sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs32.sail:21135.57-21135.58"
                    (FPCompareEQ op1 op2 (← (StandardFPSCRValue ())))) ) : SailM Bool )
              (D_set (d +i r)
                (← (Elem_set (← (D_read (d +i r))) e esize
                    (if (test_passed : Bool)
                    then (Ones (n := esize))
                    else (Zeros (n := esize))))))
              (pure (op1, op2))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, op2))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCGE_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
          let test_passed ← (( do
            if (floating_point : Bool)
            then
              (do
                sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs32.sail:21324.57-21324.58"
                let zero ← (( do (FPZero 0#1 esize) ) : SailM (BitVec esize) )
                (FPCompareGE (← (Elem_read (← (D_read (m +i r))) e esize)) zero (← (StandardFPSCRValue ()))))
            else (do (pure ((BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize))) ≥b 0))) ) : SailM Bool )
          (D_set (d +i r)
            (← (Elem_set (← (D_read (d +i r))) e esize
                (if (test_passed : Bool)
                then (Ones (n := esize))
                else (Zeros (n := esize))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCGE_r_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (vtype : VCGEType) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, op2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2) := loop_vars
      loop_vars ← do
        let (op1, op2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (n +i r))) e esize)
              let op2 ← (Elem_read (← (D_read (m +i r))) e esize)
              let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
              let test_passed ← (( do
                match vtype with
                | .VCGEType_signed => (pure ((BitVec.toInt op1) ≥b (BitVec.toInt op2)))
                | .VCGEType_unsigned => (pure ((BitVec.toNat op1) ≥b (BitVec.toNat op2)))
                | .VCGEType_fp =>
                  (do
                    sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs32.sail:21435.59-21435.60"
                    (FPCompareGE op1 op2 (← (StandardFPSCRValue ())))) ) : SailM Bool )
              let test_passed := test_passed
              (D_set (d +i r)
                (← (Elem_set (← (D_read (d +i r))) e esize
                    (if (test_passed : Bool)
                    then (Ones (n := esize))
                    else (Zeros (n := esize))))))
              (pure (op1, op2))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, op2))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCGT_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
          let test_passed ← (( do
            if (floating_point : Bool)
            then
              (do
                sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs32.sail:21630.57-21630.58"
                let zero ← (( do (FPZero 0#1 esize) ) : SailM (BitVec esize) )
                (FPCompareGT (← (Elem_read (← (D_read (m +i r))) e esize)) zero (← (StandardFPSCRValue ()))))
            else (do (pure ((BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize))) >b 0))) ) : SailM Bool )
          (D_set (d +i r)
            (← (Elem_set (← (D_read (d +i r))) e esize
                (if (test_passed : Bool)
                then (Ones (n := esize))
                else (Zeros (n := esize))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCGT_r_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (vtype : VCGTtype) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, op2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2) := loop_vars
      loop_vars ← do
        let (op1, op2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (n +i r))) e esize)
              let op2 ← (Elem_read (← (D_read (m +i r))) e esize)
              let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
              let test_passed ← (( do
                match vtype with
                | .VCGTtype_signed => (pure ((BitVec.toInt op1) >b (BitVec.toInt op2)))
                | .VCGTtype_unsigned => (pure ((BitVec.toNat op1) >b (BitVec.toNat op2)))
                | .VCGTtype_fp =>
                  (do
                    sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs32.sail:21741.59-21741.60"
                    (FPCompareGT op1 op2 (← (StandardFPSCRValue ())))) ) : SailM Bool )
              let test_passed := test_passed
              (D_set (d +i r)
                (← (Elem_set (← (D_read (d +i r))) e esize
                    (if (test_passed : Bool)
                    then (Ones (n := esize))
                    else (Zeros (n := esize))))))
              (pure (op1, op2))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, op2))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCLE_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
          let test_passed ← (( do
            if (floating_point : Bool)
            then
              (do
                sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs32.sail:21936.57-21936.58"
                let zero ← (( do (FPZero 0#1 esize) ) : SailM (BitVec esize) )
                (FPCompareGE zero (← (Elem_read (← (D_read (m +i r))) e esize)) (← (StandardFPSCRValue ()))))
            else (do (pure ((BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize))) ≤b 0))) ) : SailM Bool )
          (D_set (d +i r)
            (← (Elem_set (← (D_read (d +i r))) e esize
                (if (test_passed : Bool)
                then (Ones (n := esize))
                else (Zeros (n := esize))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCLS_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange (CountLeadingSignBits (← (Elem_read (← (D_read (m +i r))) e esize))) (esize -i 1) 0))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCLT_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
          let test_passed ← (( do
            if (floating_point : Bool)
            then
              (do
                sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs32.sail:22112.57-22112.58"
                let zero ← (( do (FPZero 0#1 esize) ) : SailM (BitVec esize) )
                (FPCompareGT zero (← (Elem_read (← (D_read (m +i r))) e esize)) (← (StandardFPSCRValue ()))))
            else (do (pure ((BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize))) <b 0))) ) : SailM Bool )
          (D_set (d +i r)
            (← (Elem_set (← (D_read (d +i r))) e esize
                (if (test_passed : Bool)
                then (Ones (n := esize))
                else (Zeros (n := esize))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCLZ_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange (CountLeadingZeroBits (← (Elem_read (← (D_read (m +i r))) e esize))) (esize -i 1) 0))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d : Nat, esize : Nat, m : Int, k_quiet_nan_exc : Bool, k_with_zero : Bool, List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCMP_Op_A_txt (d : Nat) (esize : Nat) (m : Int) (quiet_nan_exc : Bool) (with_zero : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let nzcv ← (( do
    match esize with
    | 16 =>
      (do
        let op16 ← (( do
          if (with_zero : Bool)
          then (FPZero 0#1 16)
          else (pure (Sail.BitVec.extractLsb (← (S_read m)) 15 0)) ) : SailM (BitVec 16) )
        (FPCompare (Sail.BitVec.extractLsb (← (S_read d)) 15 0) op16 quiet_nan_exc (← (FPSCR_read ()))))
    | 32 =>
      (do
        let op32 ← (( do
          if (with_zero : Bool)
          then (FPZero 0#1 32)
          else (S_read m) ) : SailM (BitVec 32) )
        (FPCompare (← (S_read d)) op32 quiet_nan_exc (← (FPSCR_read ()))))
    | 64 =>
      (do
        let op64 ← (( do
          if (with_zero : Bool)
          then (FPZero 0#1 64)
          else (D_read m) ) : SailM (BitVec 64) )
        (FPCompare (← (D_read d)) op64 quiet_nan_exc (← (FPSCR_read ()))))
    | _ => (pure nzcv) ) : SailM (BitVec 4) )
  (FPSCR_write (Mk_FPSCR_Type (Sail.BitVec.updateSubrange (← (FPSCR_read__1 ())) 31 28 nzcv)))

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 8 ∧ elements = 8 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCNT_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange (BitCount (← (Elem_read (← (D_read (m +i r))) e esize))) (esize -i 1) 0))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: k_convert_from_half : Bool, d : Nat, lowbit : Nat, m : Nat, k_uses_double : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem lowbit [0, 16] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVTB_Op_A_txt (convert_from_half : Bool) (d : Nat) (lowbit : Nat) (m : Nat) (uses_double : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  let hp ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  if (convert_from_half : Bool)
  then
    (do
      let hp ← (( do (pure (Sail.BitVec.extractLsb (← (S_read m)) (lowbit +i 15) lowbit)) ) : SailM (BitVec 16) )
      if (uses_double : Bool)
      then (D_set d (← (FPConvert__1 hp (← (FPSCR_read ())) 64)))
      else (S_set d (← (FPConvert__1 hp (← (FPSCR_read ())) 32))))
  else
    (do
      let hp ← (( do
        if (uses_double : Bool)
        then (do (FPConvert__1 (← (D_read m)) (← (FPSCR_read ())) 16))
        else (do (FPConvert__1 (← (S_read m)) (← (FPSCR_read ())) 16)) ) : SailM (BitVec 16) )
      (S_set d (Sail.BitVec.updateSubrange (← (S_read d)) (lowbit +i 15) lowbit hp)))

/-- Type quantifiers: d : Nat, k_double_to_single : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVT_ds_Op_A_txt (d : Nat) (double_to_single : Bool) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  if (double_to_single : Bool)
  then (S_set d (← (FPConvert__1 (← (D_read m)) (← (FPSCR_read ())) 32)))
  else (D_set d (← (FPConvert__1 (← (S_read m)) (← (FPSCR_read ())) 64)))

/-- Type quantifiers: d__arg : Nat, elements : Nat, k_half_to_single : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ elements = 4 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCVT_hs_Op_A_txt (d__arg : Nat) (elements : Nat) (half_to_single : Bool) (m : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if (half_to_single : Bool)
      then (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e 32 (← (FPConvert__1 (← (Elem_read (← (Din_read m)) e 16)) (← (StandardFPSCRValue ())) 32)))))
      else (D_set d (← (Elem_set (← (D_read d)) e 16 (← (FPConvert__1 (← (Elem_read (← (Qin_read (Int.shiftr m 1))) e 32)) (← (StandardFPSCRValue ())) 16)))))
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs : Nat, k_to_integer : Bool, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCVT_is_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (to_integer : Bool) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (op1, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, result) := loop_vars
      loop_vars ← do
        let (op1, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, result) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (m +i r))) e esize)
              let result ← (( do
                if (to_integer : Bool)
                then (do (FPToFixed op1 0 is_unsigned (← (StandardFPSCRValue ())) FPRounding_ZERO esize))
                else (do (FixedToFP op1 0 is_unsigned (← (StandardFPSCRValue ())) FPRounding_TIEEVEN esize)) ) : SailM (BitVec esize) )
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              (pure (op1, result))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, k_to_integer : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVT_iv_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (rounding : FPRounding) (to_integer : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_integer : Bool)
  then
    (do
      match esize with
      | 16 => (S_set d (← (FPToFixed (Sail.BitVec.extractLsb (← (S_read m)) 15 0) 0 is_unsigned (← (FPSCR_read ())) rounding 32)))
      | 32 => (S_set d (← (FPToFixed (← (S_read m)) 0 is_unsigned (← (FPSCR_read ())) rounding 32)))
      | 64 => (S_set d (← (FPToFixed (← (D_read m)) 0 is_unsigned (← (FPSCR_read ())) rounding 32)))
      | _ => (pure ()))
  else
    (do
      match esize with
      | 16 =>
        (do
          let fp16 ← (( do (FixedToFP (← (S_read m)) 0 is_unsigned (← (FPSCR_read ())) rounding 16) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ fp16)))
      | 32 => (S_set d (← (FixedToFP (← (S_read m)) 0 is_unsigned (← (FPSCR_read ())) rounding 32)))
      | 64 => (D_set d (← (FixedToFP (← (S_read m)) 0 is_unsigned (← (FPSCR_read ())) rounding 64)))
      | _ => (pure ()))

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, frac_bits : Nat, k_is_unsigned : Bool, m : Nat, regs : Nat, k_to_fixed : Bool, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ 1 ≤ frac_bits ∧ frac_bits ≤ 64 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCVT_xs_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (frac_bits : Nat) (m : Nat) (regs : Nat) (to_fixed : Bool) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (op1, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, result) := loop_vars
      loop_vars ← do
        let (op1, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, result) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (m +i r))) e esize)
              let result ← (( do
                if (to_fixed : Bool)
                then (do (FPToFixed op1 frac_bits is_unsigned (← (StandardFPSCRValue ())) FPRounding_ZERO esize))
                else (do (FixedToFP op1 frac_bits is_unsigned (← (StandardFPSCRValue ())) FPRounding_TIEEVEN esize)) ) : SailM (BitVec esize) )
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              (pure (op1, result))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d : Nat, fp_size : Nat, frac_bits : Int, k_is_unsigned : Bool, size : Nat, k_to_fixed : Bool, List.elem size [16, 32] ∧ List.elem fp_size [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVT_xv_Op_A_txt (d : Nat) (fp_size : Nat) (frac_bits : Int) (size : Nat) (to_fixed : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_fixed : Bool)
  then
    (do
      let result ← (( do (undefined_bitvector size) ) : SailM (BitVec size) )
      match fp_size with
      | 16 =>
        (do
          let result ← (( do (FPToFixed (Sail.BitVec.extractLsb (← (S_read d)) 15 0) frac_bits is_unsigned (← (FPSCR_read ())) FPRounding_ZERO size) ) : SailM (BitVec size) )
          (S_set d (← (Extend result 32 is_unsigned))))
      | 32 =>
        (do
          let result ← (( do (FPToFixed (← (S_read d)) frac_bits is_unsigned (← (FPSCR_read ())) FPRounding_ZERO size) ) : SailM (BitVec size) )
          (S_set d (← (Extend result 32 is_unsigned))))
      | 64 =>
        (do
          let result ← (( do (FPToFixed (← (D_read d)) frac_bits is_unsigned (← (FPSCR_read ())) FPRounding_ZERO size) ) : SailM (BitVec size) )
          (D_set d (← (Extend result 64 is_unsigned))))
      | _ => (pure ()))
  else
    (do
      match fp_size with
      | 16 =>
        (do
          let fp16 ← (( do (FixedToFP (Sail.BitVec.extractLsb (← (S_read d)) (size -i 1) 0) frac_bits is_unsigned (← (FPSCR_read ())) FPRounding_TIEEVEN 16) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ fp16)))
      | 32 => (S_set d (← (FixedToFP (Sail.BitVec.extractLsb (← (S_read d)) (size -i 1) 0) frac_bits is_unsigned (← (FPSCR_read ())) FPRounding_TIEEVEN 32)))
      | 64 => (D_set d (← (FixedToFP (Sail.BitVec.extractLsb (← (D_read d)) (size -i 1) 0) frac_bits is_unsigned (← (FPSCR_read ())) FPRounding_TIEEVEN 64)))
      | _ => (pure ()))

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VDIV_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 => (S_set d ((Zeros (n := 16)) +++ (← (FPDiv (Sail.BitVec.extractLsb (← (S_read n)) 15 0) (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ()))))))
  | 32 => (S_set d (← (FPDiv (← (S_read n)) (← (S_read m)) (← (FPSCR_read ())))))
  | 64 => (D_set d (← (FPDiv (← (D_read n)) (← (D_read m)) (← (FPSCR_read ())))))
  | _ => (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, regs : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ List.elem regs [1, 2] ∧ List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VDUP_r_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (regs : Nat) (t : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let scalar ← (( do (pure (Sail.BitVec.extractLsb (← (R_read t)) (esize -i 1) 0)) ) : SailM (BitVec (0 + (esize - 1 - 0 + 1))) )
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize scalar)))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, index : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VDUP_s_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (index : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let scalar ← (( do (Elem_read (← (D_read m)) index esize) ) : SailM (BitVec esize) )
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize scalar)))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VEOR_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set (d +i r) ((← (D_read (n +i r))) ^^^ (← (D_read (m +i r)))))
  (pure loop_vars)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, position : Nat, k_quadword_operation : Bool, 0 ≤ position ∧ position ≤ 120 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VEXT_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (position : Nat) (quadword_operation : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  if (quadword_operation : Bool)
  then (Q_set (Int.shiftr d 1) (Sail.BitVec.extractLsb ((← (Q_read (Int.shiftr m 1))) +++ (← (Q_read (Int.shiftr n 1)))) (position +i 127) position))
  else
    (do
      sail_assert ((0 ≤b position) && ((position ≤b (position +i 63)) && ((position +i 63) <b 128))) "src/instrs32.sail:23935.96-23935.97"
      (D_set d (Sail.BitVec.extractLsb ((← (D_read m)) +++ (← (D_read n))) (position +i 63) position)))

/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, regs : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VFMA_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  let op16 ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  let op32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let op64 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let loop_r_lower := 0
      let loop_r_upper := (regs -i 1)
      let mut loop_vars := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (( do (Elem_read (← (D_read (n +i r))) e esize) ) : SailM (BitVec esize) )
              let op1 ← (( do
                if (op1_neg : Bool)
                then (do (FPNeg op1))
                else (pure op1) ) : SailM (BitVec esize) )
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPMulAdd (← (Elem_read (← (D_read (d +i r))) e esize)) op1 (← (Elem_read (← (D_read (m +i r))) e esize)) (← (StandardFPSCRValue ())))))))
          (pure loop_vars_1)
      (pure loop_vars))
  else
    (do
      match esize with
      | 16 =>
        (do
          let op16 ← (( do
            if (op1_neg : Bool)
            then (FPNeg (Sail.BitVec.extractLsb (← (S_read n)) 15 0))
            else (pure (Sail.BitVec.extractLsb (← (S_read n)) 15 0)) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ (← (FPMulAdd (Sail.BitVec.extractLsb (← (S_read d)) 15 0) op16 (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ())))))))
      | 32 =>
        (do
          let op32 ← (( do
            if (op1_neg : Bool)
            then (FPNeg (← (S_read n)))
            else (S_read n) ) : SailM (BitVec 32) )
          (S_set d (← (FPMulAdd (← (S_read d)) op32 (← (S_read m)) (← (FPSCR_read ()))))))
      | 64 =>
        (do
          let op64 ← (( do
            if (op1_neg : Bool)
            then (FPNeg (← (D_read n)))
            else (D_read n) ) : SailM (BitVec 64) )
          (D_set d (← (FPMulAdd (← (D_read d)) op64 (← (D_read m)) (← (FPSCR_read ()))))))
      | _ => (pure ()))

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VFNMA_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  let op16 ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  let op32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let op64 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (do
      let op16 ← (( do
        if (op1_neg : Bool)
        then (FPNeg (Sail.BitVec.extractLsb (← (S_read n)) 15 0))
        else (pure (Sail.BitVec.extractLsb (← (S_read n)) 15 0)) ) : SailM (BitVec 16) )
      (S_set d ((Zeros (n := 16)) +++ (← (FPMulAdd (← (FPNeg (Sail.BitVec.extractLsb (← (S_read d)) 15 0))) op16 (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ())))))))
  | 32 =>
    (do
      let op32 ← (( do
        if (op1_neg : Bool)
        then (FPNeg (← (S_read n)))
        else (S_read n) ) : SailM (BitVec 32) )
      (S_set d (← (FPMulAdd (← (FPNeg (← (S_read d)))) op32 (← (S_read m)) (← (FPSCR_read ()))))))
  | 64 =>
    (do
      let op64 ← (( do
        if (op1_neg : Bool)
        then (FPNeg (← (D_read n)))
        else (D_read n) ) : SailM (BitVec 64) )
      (D_set d (← (FPMulAdd (← (FPNeg (← (D_read d)))) op64 (← (D_read m)) (← (FPSCR_read ()))))))
  | _ => (pure ())

/-- Type quantifiers: k_add : Bool, d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VHADD_Op_A_txt (add : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let (op1, op2, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2, result) := loop_vars
      loop_vars ← do
        let (op1, op2, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2, result) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (asl_Int (← (Elem_read (← (D_read (n +i r))) e esize)) is_unsigned)
              let op2 ← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)
              let result : Int :=
                if (add : Bool)
                then (Int.shiftr (op1 +i op2) 1)
                else (Int.shiftr (op1 -i op2) 1)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange result (esize -i 1) 0))))
              (pure (op1, op2, result))
          (pure loop_vars_1) ) : SailM (Int × Int × Int) )
        (pure (op1, op2, result))
    (pure loop_vars) ) : SailM (Int × Int × Int) )
  (pure ())

/-- Type quantifiers: alignment : Nat, d__arg : Nat, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem ebytes [1, 2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 2, 4] -/
def execute_aarch32_instrs_VLD1_1_Op_A_txt (alignment : Nat) (d__arg : Nat) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  (D_set d (← (Elem_set (← (D_read d)) index (8 *i ebytes) (← (MemU_read address ebytes)))))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) ebytes)))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d : Nat, ebytes : Nat, m : Nat, n : Nat, k_register_index : Bool, regs : Nat, k_wback : Bool, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 2, 4, 8] -/
def execute_aarch32_instrs_VLD1_a_Op_A_txt (alignment : Nat) (d : Nat) (ebytes : Nat) (m : Nat) (n : Nat) (register_index : Bool) (regs : Nat) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let esize := (8 *i ebytes)
  let element ← (( do (MemU_read address ebytes) ) : SailM (BitVec esize) )
  let replicated_element : (BitVec 64) := (BitVec.replicateBits element (Int.ediv 64 esize))
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set (d +i r) replicated_element)
  (pure loop_vars)
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) ebytes)))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d__arg : Nat, ebytes : Nat, elements : Int, m : Nat, n : Nat, k_register_index : Bool, regs : Nat, k_wback : Bool, List.elem regs [1, 2, 3, 4] ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VLD1_m_Op_A_txt (alignment : Nat) (d__arg : Nat) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (regs : Nat) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let address ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := address
    for r in [loop_r_lower:loop_r_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := address
        for e in [loop_e_lower:loop_e_upper:1]i do
          let address := loop_vars_1
          loop_vars_1 ← do
            let data ← (( do (undefined_bitvector (ebytes *i 8)) ) : SailM (BitVec (ebytes * 8)) )
            let data ← (( do
              if ((ebytes != 8) : Bool)
              then (do (MemU_read address ebytes))
              else
                (do
                  if ((←((pure (! (IsAligned__1 address ebytes))) <&&> (do
                       (AlignmentEnforced ())))) : Bool)
                  then (AArch32_Abort address (← (AlignmentFault accdesc)))
                  else (pure ())
                  if ((← (BigEndian AccessType_ASIMD)) : Bool)
                  then
                    (do
                      let data ← (pure (Sail.BitVec.updateSubrange data 31 0 (← (MemU_read (BitVec.addInt address 4) 4))))
                      (pure (Sail.BitVec.updateSubrange data 63 32 (← (MemU_read address 4)))))
                  else
                    (do
                      let data ← (pure (Sail.BitVec.updateSubrange data 31 0 (← (MemU_read address 4))))
                      (pure (Sail.BitVec.updateSubrange data 63 32 (← (MemU_read (BitVec.addInt address 4) 4)))))) ) : SailM (BitVec (ebytes * 8)) )
            (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e (8 *i ebytes) data)))
            (pure (BitVec.addInt address ebytes))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (8 *i regs))))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d__arg : Nat, d2__arg : Int, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem ebytes [1, 2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 2, 4, 8] -/
def execute_aarch32_instrs_VLD2_1_Op_A_txt (alignment : Nat) (d__arg : Nat) (d2__arg : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  (D_set d (← (Elem_set (← (D_read d)) index (8 *i ebytes) (← (MemU_read address ebytes)))))
  (D_set d2 (← (Elem_set (← (D_read d2)) index (8 *i ebytes) (← (MemU_read (BitVec.addInt address ebytes) ebytes)))))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (2 *i ebytes))))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, ebytes : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 2, 4, 8, 16] -/
def execute_aarch32_instrs_VLD2_a_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (ebytes : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let esize := (8 *i ebytes)
  let element1 ← (( do (MemU_read address ebytes) ) : SailM (BitVec esize) )
  let element2 ← (( do (MemU_read (BitVec.addInt address ebytes) ebytes) ) : SailM (BitVec esize) )
  (D_set d (BitVec.replicateBits element1 (Int.ediv 64 esize)))
  (D_set d2 (BitVec.replicateBits element2 (Int.ediv 64 esize)))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (2 *i ebytes))))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d__arg : Nat, d2__arg : Int, ebytes : Nat, elements : Int, m : Nat, n : Nat, pairs : Nat, k_register_index : Bool, k_wback : Bool, List.elem pairs [1, 2] ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VLD2_m_Op_A_txt (alignment : Nat) (d__arg : Nat) (d2__arg : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (pairs : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let address ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (pairs -i 1)
    let mut loop_vars := address
    for r in [loop_r_lower:loop_r_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := address
        for e in [loop_e_lower:loop_e_upper:1]i do
          let address := loop_vars_1
          loop_vars_1 ← do
            (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e (8 *i ebytes) (← (MemU_read address ebytes)))))
            (D_set (d2 +i r) (← (Elem_set (← (D_read (d2 +i r))) e (8 *i ebytes) (← (MemU_read (BitVec.addInt address ebytes) ebytes)))))
            (pure (BitVec.addInt address (2 *i ebytes)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (16 *i pairs))))
  else (pure ())

/-- Type quantifiers: d__arg : Nat, d2__arg : Int, d3__arg : Int, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem ebytes [1, 2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VLD3_1_Op_A_txt (d__arg : Nat) (d2__arg : Int) (d3__arg : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
  let d3 : Int := d3__arg
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (D_set d (← (Elem_set (← (D_read d)) index (8 *i ebytes) (← (MemU_read address ebytes)))))
  (D_set d2 (← (Elem_set (← (D_read d2)) index (8 *i ebytes) (← (MemU_read (BitVec.addInt address ebytes) ebytes)))))
  (D_set d3 (← (Elem_set (← (D_read d3)) index (8 *i ebytes) (← (MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes)))))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (3 *i ebytes))))
  else (pure ())

/-- Type quantifiers: d : Nat, d2 : Int, d3 : Int, ebytes : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VLD3_a_Op_A_txt (d : Nat) (d2 : Int) (d3 : Int) (ebytes : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let esize := (ebytes *i 8)
  let element1 ← (( do (MemU_read address ebytes) ) : SailM (BitVec esize) )
  let element2 ← (( do (MemU_read (BitVec.addInt address ebytes) ebytes) ) : SailM (BitVec esize) )
  let element3 ← (( do (MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes) ) : SailM (BitVec esize) )
  (D_set d (BitVec.replicateBits element1 (Int.ediv 64 esize)))
  (D_set d2 (BitVec.replicateBits element2 (Int.ediv 64 esize)))
  (D_set d3 (BitVec.replicateBits element3 (Int.ediv 64 esize)))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (3 *i ebytes))))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d__arg : Nat, d2__arg : Int, d3__arg : Int, ebytes : Nat, elements : Int, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 8] -/
def execute_aarch32_instrs_VLD3_m_Op_A_txt (alignment : Nat) (d__arg : Nat) (d2__arg : Int) (d3__arg : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
  let d3 : Int := d3__arg
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let address ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := address
    for e in [loop_e_lower:loop_e_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        (D_set d (← (Elem_set (← (D_read d)) e (8 *i ebytes) (← (MemU_read address ebytes)))))
        (D_set d2 (← (Elem_set (← (D_read d2)) e (8 *i ebytes) (← (MemU_read (BitVec.addInt address ebytes) ebytes)))))
        (D_set d3 (← (Elem_set (← (D_read d3)) e (8 *i ebytes) (← (MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes)))))
        (pure (BitVec.addInt address (3 *i ebytes)))
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) 24)))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d__arg : Nat, d2__arg : Int, d3__arg : Int, d4__arg : Int, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem ebytes [1, 2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VLD4_1_Op_A_txt (alignment : Nat) (d__arg : Nat) (d2__arg : Int) (d3__arg : Int) (d4__arg : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
  let d3 : Int := d3__arg
  let d4 : Int := d4__arg
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  (D_set d (← (Elem_set (← (D_read d)) index (8 *i ebytes) (← (MemU_read address ebytes)))))
  (D_set d2 (← (Elem_set (← (D_read d2)) index (8 *i ebytes) (← (MemU_read (BitVec.addInt address ebytes) ebytes)))))
  (D_set d3 (← (Elem_set (← (D_read d3)) index (8 *i ebytes) (← (MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes)))))
  (D_set d4 (← (Elem_set (← (D_read d4)) index (8 *i ebytes) (← (MemU_read (BitVec.addInt address (3 *i ebytes)) ebytes)))))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (4 *i ebytes))))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, d3 : Int, d4 : Int, ebytes : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VLD4_a_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (d3 : Int) (d4 : Int) (ebytes : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let esize := (ebytes *i 8)
  let element1 ← (( do (MemU_read address ebytes) ) : SailM (BitVec esize) )
  let element2 ← (( do (MemU_read (BitVec.addInt address ebytes) ebytes) ) : SailM (BitVec esize) )
  let element3 ← (( do (MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes) ) : SailM (BitVec esize) )
  let element4 ← (( do (MemU_read (BitVec.addInt address (3 *i ebytes)) ebytes) ) : SailM (BitVec esize) )
  (D_set d (BitVec.replicateBits element1 (Int.ediv 64 esize)))
  (D_set d2 (BitVec.replicateBits element2 (Int.ediv 64 esize)))
  (D_set d3 (BitVec.replicateBits element3 (Int.ediv 64 esize)))
  (D_set d4 (BitVec.replicateBits element4 (Int.ediv 64 esize)))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (4 *i ebytes))))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d__arg : Nat, d2__arg : Int, d3__arg : Int, d4__arg : Int, ebytes : Nat, elements : Int, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VLD4_m_Op_A_txt (alignment : Nat) (d__arg : Nat) (d2__arg : Int) (d3__arg : Int) (d4__arg : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  let d : Int := d__arg
  let d2 : Int := d2__arg
  let d3 : Int := d3__arg
  let d4 : Int := d4__arg
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let address ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := address
    for e in [loop_e_lower:loop_e_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        (D_set d (← (Elem_set (← (D_read d)) e (8 *i ebytes) (← (MemU_read address ebytes)))))
        (D_set d2 (← (Elem_set (← (D_read d2)) e (8 *i ebytes) (← (MemU_read (BitVec.addInt address ebytes) ebytes)))))
        (D_set d3 (← (Elem_set (← (D_read d3)) e (8 *i ebytes) (← (MemU_read (BitVec.addInt address (2 *i ebytes)) ebytes)))))
        (D_set d4 (← (Elem_set (← (D_read d4)) e (8 *i ebytes) (← (MemU_read (BitVec.addInt address (3 *i ebytes)) ebytes)))))
        (pure (BitVec.addInt address (4 *i ebytes)))
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) 32)))
  else (pure ())

/-- Type quantifiers: k_add : Bool, d : Nat, n : Nat, regs : Int, k_single_regs : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VLDM_Op_A_txt (add : Bool) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (regs : Int) (single_regs : Bool) (wback : Bool) : SailM Unit := do
  let word1 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let word2 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  (CheckVFPEnabled true)
  let address ← (( do
    if (add : Bool)
    then (R_read n)
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let (address, word1, word2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (address, word1, word2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (address, word1, word2) := loop_vars
      loop_vars ← do
        let (address, word1, word2) ← (( do
          if (single_regs : Bool)
          then
            (do
              (S_set (d +i r) (← (MemA_read address 4)))
              let address : (BitVec 32) := (BitVec.addInt address 4)
              (pure (address, word1, word2)))
          else
            (do
              let word1 ← (MemA_read address 4)
              let word2 ← (MemA_read (BitVec.addInt address 4) 4)
              let address : (BitVec 32) := (BitVec.addInt address 8)
              (D_set (d +i r)
                (← (do
                  if ((← (BigEndian AccessType_ASIMD)) : Bool)
                  then (pure (word1 +++ word2))
                  else (pure (word2 +++ word1)))))
              (pure (address, word1, word2))) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) )
        (pure (address, word1, word2))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) )
  if (wback : Bool)
  then
    (R_set n
      (← (do
        if (add : Bool)
        then (pure ((← (R_read n)) + imm32))
        else (pure ((← (R_read n)) - imm32)))))
  else (pure ())

/-- Type quantifiers: k_add : Bool, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VLDR_Op_A_txt (add : Bool) (d : Nat) (esize : Nat) (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let word1 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let word2 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  (CheckVFPEnabled true)
  let base ← (( do
    if ((n == 15) : Bool)
    then (pure (Align_bits (← (PC_read__1 ())) 4))
    else (R_read n) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  match esize with
  | 16 => (S_set d ((Zeros (n := 16)) +++ (← (MemA_read address 2))))
  | 32 => (S_set d (← (MemA_read address 4)))
  | 64 =>
    (do
      let word1 ← (( do (MemA_read address 4) ) : SailM (BitVec 32) )
      let word2 ← (( do (MemA_read (BitVec.addInt address 4) 4) ) : SailM (BitVec 32) )
      (D_set d
        (← (do
          if ((← (BigEndian AccessType_ASIMD)) : Bool)
          then (pure (word1 +++ word2))
          else (pure (word2 +++ word1))))))
  | _ => (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, k_maximum : Bool, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMAX_f_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (maximum : Bool) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, op2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2) := loop_vars
      loop_vars ← do
        let (op1, op2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (n +i r))) e esize)
              let op2 ← (Elem_read (← (D_read (m +i r))) e esize)
              if (maximum : Bool)
              then (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPMax op1 op2 (← (StandardFPSCRValue ())))))))
              else (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPMin op1 op2 (← (StandardFPSCRValue ())))))))
              (pure (op1, op2))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, op2))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, k_maximum : Bool, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMAX_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (maximum : Bool) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let (op1, op2, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2, result) := loop_vars
      loop_vars ← do
        let (op1, op2, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2, result) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (asl_Int (← (Elem_read (← (D_read (n +i r))) e esize)) is_unsigned)
              let op2 ← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)
              let result : Int :=
                if (maximum : Bool)
                then (Max.max op1 op2)
                else (Min.min op1 op2)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange result (esize -i 1) 0))))
              (pure (op1, op2, result))
          (pure loop_vars_1) ) : SailM (Int × Int × Int) )
        (pure (op1, op2, result))
    (pure loop_vars) ) : SailM (Int × Int × Int) )
  (pure ())

/-- Type quantifiers: k_add : Bool, k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMLA_f_Op_A_txt (add : Bool) (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  let addend ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let addend16 ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  let addend32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let addend64 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let product ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let (addend, product) ← (( do
        let loop_r_lower := 0
        let loop_r_upper := (regs -i 1)
        let mut loop_vars := (addend, product)
        for r in [loop_r_lower:loop_r_upper:1]i do
          let (addend, product) := loop_vars
          loop_vars ← do
            let (addend, product) ← (( do
              let loop_e_lower := 0
              let loop_e_upper := (elements -i 1)
              let mut loop_vars_1 := (addend, product)
              for e in [loop_e_lower:loop_e_upper:1]i do
                let (addend, product) := loop_vars_1
                loop_vars_1 ← do
                  let product ← (FPMul (← (Elem_read (← (D_read (n +i r))) e esize)) (← (Elem_read (← (D_read (m +i r))) e esize)) (← (StandardFPSCRValue ())))
                  let addend ←
                    if (add : Bool)
                    then (pure product)
                    else (FPNeg product)
                  (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPAdd (← (Elem_read (← (D_read (d +i r))) e esize)) addend (← (StandardFPSCRValue ())))))))
                  (pure (addend, product))
              (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
            (pure (addend, product))
        (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
      (pure ()))
  else
    (do
      match esize with
      | 16 =>
        (do
          let addend16 ← (( do
            if (add : Bool)
            then (FPMul (Sail.BitVec.extractLsb (← (S_read n)) 15 0) (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ())))
            else (FPNeg (← (FPMul (Sail.BitVec.extractLsb (← (S_read n)) 15 0) (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ()))))) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ (← (FPAdd (Sail.BitVec.extractLsb (← (S_read d)) 15 0) addend16 (← (FPSCR_read ())))))))
      | 32 =>
        (do
          let addend32 ← (( do
            if (add : Bool)
            then (FPMul (← (S_read n)) (← (S_read m)) (← (FPSCR_read ())))
            else (FPNeg (← (FPMul (← (S_read n)) (← (S_read m)) (← (FPSCR_read ()))))) ) : SailM (BitVec 32) )
          (S_set d (← (FPAdd (← (S_read d)) addend32 (← (FPSCR_read ()))))))
      | 64 =>
        (do
          let addend64 ← (( do
            if (add : Bool)
            then (FPMul (← (D_read n)) (← (D_read m)) (← (FPSCR_read ())))
            else (FPNeg (← (FPMul (← (D_read n)) (← (D_read m)) (← (FPSCR_read ()))))) ) : SailM (BitVec 64) )
          (D_set d (← (FPAdd (← (D_read d)) addend64 (← (FPSCR_read ()))))))
      | _ => (pure ()))

/-- Type quantifiers: k_add : Bool, d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_long_destination : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMLA_i_Op_A_txt (add : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let addend ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let (addend, product) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (addend, product)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (addend, product) := loop_vars
      loop_vars ← do
        let (addend, product) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (addend, product)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (addend, product) := loop_vars_1
            loop_vars_1 ← do
              let product ← (pure ((← (asl_Int (← (Elem_read (← (Din_read (n +i r))) e esize)) is_unsigned)) *i (← (asl_Int (← (Elem_read (← (Din_read (m +i r))) e esize)) is_unsigned))))
              let addend : Int :=
                if (add : Bool)
                then product
                else (Neg.neg product)
              if (long_destination : Bool)
              then (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) (BitVec.addInt (← (Elem_read (← (Qin_read (Int.shiftr d 1))) e (2 *i esize))) addend))))
              else (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (BitVec.addInt (← (Elem_read (← (Din_read (d +i r))) e esize)) addend))))
              (pure (addend, product))
          (pure loop_vars_1) ) : SailM (Int × Int) )
        (pure (addend, product))
    (pure loop_vars) ) : SailM (Int × Int) )
  (pure ())

/-- Type quantifiers: k_add : Bool, d__arg : Nat, elements : Nat, esize : Nat, k_floating_point : Bool, index : Nat, k_is_unsigned : Bool, k_long_destination : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMLA_s_Op_A_txt (add : Bool) (d__arg : Nat) (elements : Nat) (esize : Nat) (floating_point : Bool) (index : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let addend ← (( do (undefined_int ()) ) : SailM Int )
  let fp_addend ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op1val ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (Elem_read (← (Din_read m)) index esize) ) : SailM (BitVec esize) )
  let op2val ← do (asl_Int op2 is_unsigned)
  let (addend, fp_addend, op1, op1val) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (addend, fp_addend, op1, op1val)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (addend, fp_addend, op1, op1val) := loop_vars
      loop_vars ← do
        let (addend, fp_addend, op1, op1val) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (addend, fp_addend, op1, op1val)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (addend, fp_addend, op1, op1val) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (Din_read (n +i r))) e esize)
              let op1val ← (asl_Int op1 is_unsigned)
              let (addend, fp_addend) ← (( do
                if (floating_point : Bool)
                then
                  (do
                    let fp_addend ←
                      if (add : Bool)
                      then (FPMul op1 op2 (← (StandardFPSCRValue ())))
                      else (FPNeg (← (FPMul op1 op2 (← (StandardFPSCRValue ())))))
                    (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPAdd (← (Elem_read (← (Din_read (d +i r))) e esize)) fp_addend (← (StandardFPSCRValue ())))))))
                    (pure (addend, fp_addend)))
                else
                  (do
                    let addend : Int :=
                      if (add : Bool)
                      then (op1val *i op2val)
                      else ((Neg.neg op1val) *i op2val)
                    if (long_destination : Bool)
                    then (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) (BitVec.addInt (← (Elem_read (← (Qin_read (Int.shiftr d 1))) e (2 *i esize))) addend))))
                    else (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (BitVec.addInt (← (Elem_read (← (Din_read (d +i r))) e esize)) addend))))
                    (pure (addend, fp_addend))) ) : SailM (Int × (BitVec esize)) )
              (pure (addend, fp_addend, op1, op1val))
          (pure loop_vars_1) ) : SailM (Int × (BitVec esize) × (BitVec esize) × Int) )
        (pure (addend, fp_addend, op1, op1val))
    (pure loop_vars) ) : SailM (Int × (BitVec esize) × (BitVec esize) × Int) )
  (pure ())

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMOVX_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  (S_set d ((Zeros (n := 16)) +++ (Sail.BitVec.extractLsb (← (S_read m)) 31 16)))

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VINS_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  (S_set d ((Sail.BitVec.extractLsb (← (S_read m)) 15 0) +++ (Sail.BitVec.extractLsb (← (S_read d)) 15 0)))

/-- Type quantifiers: m : Nat, t : Nat, t2 : Nat, k_to_arm_registers : Bool, 0 ≤ t2 ∧ t2 ≤ 15 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ m ∧ m ≤ 31 -/
def execute_aarch32_instrs_VMOV_d_Op_A_txt (m : Nat) (t : Nat) (t2 : Nat) (to_arm_registers : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_arm_registers : Bool)
  then
    (do
      (R_set t (Sail.BitVec.extractLsb (← (D_read m)) 31 0))
      (R_set t2 (Sail.BitVec.extractLsb (← (D_read m)) 63 32)))
  else
    (do
      (D_set m (Sail.BitVec.updateSubrange (← (D_read m)) 31 0 (← (R_read t))))
      (D_set m (Sail.BitVec.updateSubrange (← (D_read m)) 63 32 (← (R_read t2)))))

/-- Type quantifiers: k_advsimd : Bool, d : Nat, regs : Nat, k_single_register : Bool, List.elem regs [1, 2] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMOV_i_Op_A_txt (advsimd : Bool) (d : Nat) (imm32 : (BitVec 32)) (imm64 : (BitVec 64)) (regs : Nat) (single_register : Bool) : SailM Unit := do
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (single_register : Bool)
  then (S_set d imm32)
  else
    (do
      let loop_r_lower := 0
      let loop_r_upper := (regs -i 1)
      let mut loop_vars := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars
        loop_vars ← do (D_set (d +i r) imm64)
      (pure loop_vars))

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [0, 8, 16, 24, 32, 40, 48, 56] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMOVL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        sail_assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || (! ((e ≥b 0) && (((e +i 1) *i esize) ≤b 64)))) "src/instrs32.sail:28727.131-28727.132"
        let result ← (asl_Int (← (Elem_read (← (Din_read m)) e esize)) is_unsigned)
        (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) (integer_subrange result ((2 *i esize) -i 1) 0))))
        (pure result)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMOVN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set d (← (Elem_set (← (D_read d)) e esize (Sail.BitVec.extractLsb (← (Elem_read (← (Qin_read (Int.shiftr m 1))) e (2 *i esize))) (esize -i 1) 0))))
  (pure loop_vars)

/-- Type quantifiers: n : Nat, t : Nat, k_to_arm_register : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch32_instrs_VMOV_h_Op_A_txt (n : Nat) (t : Nat) (to_arm_register : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_arm_register : Bool)
  then (R_set t ((Zeros (n := 16)) +++ (Sail.BitVec.extractLsb (← (S_read n)) 15 0)))
  else (S_set n ((Zeros (n := 16)) +++ (Sail.BitVec.extractLsb (← (R_read t)) 15 0)))

/-- Type quantifiers: k_advsimd : Bool, d : Nat, m : Nat, regs : Nat, k_single_register : Bool, regs = 1 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMOV_r_Op_A_txt (advsimd : Bool) (d : Nat) (m : Nat) (regs : Nat) (single_register : Bool) : SailM Unit := do
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (single_register : Bool)
  then (S_set d (← (S_read m)))
  else
    (do
      let loop_r_lower := 0
      let loop_r_upper := (regs -i 1)
      let mut loop_vars := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars
        loop_vars ← do (D_set (d +i r) (← (D_read (m +i r))))
      (pure loop_vars))

/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, esize : Nat, index : Int, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMOV_rs_Op_A_txt (advsimd : Bool) (d__arg : Nat) (esize : Nat) (index : Int) (t : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  (D_set d (← (Elem_set (← (D_read d)) index esize (Sail.BitVec.extractLsb (← (R_read t)) (esize -i 1) 0))))

/-- Type quantifiers: n : Nat, t : Nat, k_to_arm_register : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch32_instrs_VMOV_s_Op_A_txt (n : Nat) (t : Nat) (to_arm_register : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_arm_register : Bool)
  then (R_set t (← (S_read n)))
  else (S_set n (← (R_read t)))

/-- Type quantifiers: k_advsimd : Bool, esize : Nat, index : Int, k_is_unsigned : Bool, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] -/
def execute_aarch32_instrs_VMOV_sr_Op_A_txt (advsimd : Bool) (esize : Nat) (index : Int) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (is_unsigned : Bool)
  then (R_set t (Sail.BitVec.zeroExtend (← (Elem_read (← (D_read n)) index esize)) 32))
  else (R_set t (sign_extend (← (Elem_read (← (D_read n)) index esize)) 32))

/-- Type quantifiers: m : Nat, t : Nat, t2 : Nat, k_to_arm_registers : Bool, 0 ≤ t2 ∧ t2 ≤ 15 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ m ∧ m ≤ 31 -/
def execute_aarch32_instrs_VMOV_ss_Op_A_txt (m : Nat) (t : Nat) (t2 : Nat) (to_arm_registers : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_arm_registers : Bool)
  then
    (do
      (R_set t (← (S_read m)))
      (R_set t2 (← (S_read (m +i 1)))))
  else
    (do
      (S_set m (← (R_read t)))
      (S_set (m +i 1) (← (R_read t2))))

/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMUL_f_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let loop_r_lower := 0
      let loop_r_upper := (regs -i 1)
      let mut loop_vars := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPMul (← (Elem_read (← (D_read (n +i r))) e esize)) (← (Elem_read (← (D_read (m +i r))) e esize)) (← (StandardFPSCRValue ())))))))
          (pure loop_vars_1)
      (pure loop_vars))
  else
    (do
      match esize with
      | 16 => (S_set d ((Zeros (n := 16)) +++ (← (FPMul (Sail.BitVec.extractLsb (← (S_read n)) 15 0) (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ()))))))
      | 32 => (S_set d (← (FPMul (← (S_read n)) (← (S_read m)) (← (FPSCR_read ())))))
      | 64 => (D_set d (← (FPMul (← (D_read n)) (← (D_read m)) (← (FPSCR_read ())))))
      | _ => (pure ()))

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_long_destination : Bool, m : Nat, n : Nat, k_polynomial : Bool, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMUL_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (polynomial : Bool) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op1val ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2val ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let (op1, op1val, op2, op2val) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op1val, op2, op2val)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op1val, op2, op2val) := loop_vars
      loop_vars ← do
        let (op1, op1val, op2, op2val) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op1val, op2, op2val)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op1val, op2, op2val) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (Din_read (n +i r))) e esize)
              let op1val ← (asl_Int op1 is_unsigned)
              let op2 ← (Elem_read (← (Din_read (m +i r))) e esize)
              let op2val ← (asl_Int op2 is_unsigned)
              let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
              let product : (BitVec (2 * esize)) :=
                if (polynomial : Bool)
                then (PolynomialMult op1 op2)
                else (integer_subrange (op1val *i op2val) ((2 *i esize) -i 1) 0)
              if (long_destination : Bool)
              then (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) product)))
              else (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (Sail.BitVec.extractLsb product (esize -i 1) 0))))
              (pure (op1, op1val, op2, op2val))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × Int × (BitVec esize) × Int) )
        (pure (op1, op1val, op2, op2val))
    (pure loop_vars) ) : SailM ((BitVec esize) × Int × (BitVec esize) × Int) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_floating_point : Bool, index : Nat, k_is_unsigned : Bool, k_long_destination : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMUL_s_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (floating_point : Bool) (index : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op1val ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (Elem_read (← (Din_read m)) index esize) ) : SailM (BitVec esize) )
  let op2val ← do (asl_Int op2 is_unsigned)
  let (op1, op1val) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op1val)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op1val) := loop_vars
      loop_vars ← do
        let (op1, op1val) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op1val)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op1val) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (Din_read (n +i r))) e esize)
              let op1val ← (asl_Int op1 is_unsigned)
              if (floating_point : Bool)
              then (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPMul op1 op2 (← (StandardFPSCRValue ())))))))
              else
                (do
                  if (long_destination : Bool)
                  then (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) (integer_subrange (op1val *i op2val) ((2 *i esize) -i 1) 0))))
                  else (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange (op1val *i op2val) (esize -i 1) 0)))))
              (pure (op1, op1val))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × Int) )
        (pure (op1, op1val))
    (pure loop_vars) ) : SailM ((BitVec esize) × Int) )
  (pure ())

/-- Type quantifiers: d : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMVN_i_Op_A_txt (d : Nat) (imm64 : (BitVec 64)) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set (d +i r) (Complement.complement imm64))
  (pure loop_vars)

/-- Type quantifiers: d : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMVN_r_Op_A_txt (d : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set (d +i r) (Complement.complement (← (D_read (m +i r)))))
  (pure loop_vars)

/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, k_floating_point : Bool, m : Nat, regs : Int, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VNEG_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let result ← (( do
        let loop_r_lower := 0
        let loop_r_upper := (regs -i 1)
        let mut loop_vars := result
        for r in [loop_r_lower:loop_r_upper:1]i do
          let result := loop_vars
          loop_vars ← do
            let loop_e_lower := 0
            let loop_e_upper := (elements -i 1)
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                if (floating_point : Bool)
                then
                  (do
                    sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs32.sail:30507.61-30507.62"
                    (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPNeg (← (Elem_read (← (D_read (m +i r))) e esize)))))))
                    (pure result))
                else
                  (do
                    let result ← (pure (Neg.neg (BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize)))))
                    (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange result (esize -i 1) 0))))
                    (pure result))
            (pure loop_vars_1)
        (pure loop_vars) ) : SailM Int )
      (pure ()))
  else
    (do
      match esize with
      | 16 => (S_set d ((Zeros (n := 16)) +++ (← (FPNeg (Sail.BitVec.extractLsb (← (S_read m)) 15 0)))))
      | 32 => (S_set d (← (FPNeg (← (S_read m)))))
      | 64 => (D_set d (← (FPNeg (← (D_read m)))))
      | _ => (pure ()))

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VNMLA_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (vtype : VFPNegMul) : SailM Unit := do
  let product16 ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  let product32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let product64 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (do
      let product16 ← (( do (FPMul (Sail.BitVec.extractLsb (← (S_read n)) 15 0) (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ()))) ) : SailM (BitVec 16) )
      match vtype with
      | .VFPNegMul_VNMLA => (S_set d ((Zeros (n := 16)) +++ (← (FPAdd (← (FPNeg (Sail.BitVec.extractLsb (← (S_read d)) 15 0))) (← (FPNeg product16)) (← (FPSCR_read ()))))))
      | .VFPNegMul_VNMLS => (S_set d ((Zeros (n := 16)) +++ (← (FPAdd (← (FPNeg (Sail.BitVec.extractLsb (← (S_read d)) 15 0))) product16 (← (FPSCR_read ()))))))
      | .VFPNegMul_VNMUL => (S_set d ((Zeros (n := 16)) +++ (← (FPNeg product16)))))
  | 32 =>
    (do
      let product32 ← (( do (FPMul (← (S_read n)) (← (S_read m)) (← (FPSCR_read ()))) ) : SailM (BitVec 32) )
      match vtype with
      | .VFPNegMul_VNMLA => (S_set d (← (FPAdd (← (FPNeg (← (S_read d)))) (← (FPNeg product32)) (← (FPSCR_read ())))))
      | .VFPNegMul_VNMLS => (S_set d (← (FPAdd (← (FPNeg (← (S_read d)))) product32 (← (FPSCR_read ())))))
      | .VFPNegMul_VNMUL => (S_set d (← (FPNeg product32))))
  | 64 =>
    (do
      let product64 ← (( do (FPMul (← (D_read n)) (← (D_read m)) (← (FPSCR_read ()))) ) : SailM (BitVec 64) )
      match vtype with
      | .VFPNegMul_VNMLA => (D_set d (← (FPAdd (← (FPNeg (← (D_read d)))) (← (FPNeg product64)) (← (FPSCR_read ())))))
      | .VFPNegMul_VNMLS => (D_set d (← (FPAdd (← (FPNeg (← (D_read d)))) product64 (← (FPSCR_read ())))))
      | .VFPNegMul_VNMUL => (D_set d (← (FPNeg product64))))
  | _ => (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VORN_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set (d +i r) ((← (D_read (n +i r))) ||| (Complement.complement (← (D_read (m +i r))))))
  (pure loop_vars)

/-- Type quantifiers: d : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VORR_i_Op_A_txt (d : Nat) (imm64 : (BitVec 64)) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set (d +i r) ((← (D_read (d +i r))) ||| imm64))
  (pure loop_vars)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VORR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do (D_set (d +i r) ((← (D_read (n +i r))) ||| (← (D_read (m +i r)))))
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VPADAL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let h := (fdiv_int elements 2)
  let (op1, op2, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2, result) := loop_vars
      loop_vars ← do
        let (op1, op2, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (h -i 1)
          let mut loop_vars_1 := (op1, op2, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2, result) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (m +i r))) (2 *i e) esize)
              let op2 ← (Elem_read (← (D_read (m +i r))) ((2 *i e) +i 1) esize)
              let result ← (pure ((← (asl_Int op1 is_unsigned)) +i (← (asl_Int op2 is_unsigned))))
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e (2 *i esize) (BitVec.addInt (← (Elem_read (← (D_read (d +i r))) e (2 *i esize))) result))))
              (pure (op1, op2, result))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize) × Int) )
        (pure (op1, op2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × Int) )
  (pure ())

/-- Type quantifiers: d : Nat, elements : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VPADD_f_Op_A_txt (d : Nat) (elements : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let dest ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let h := (Int.ediv elements 2)
  let dest ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (h -i 1)
    let mut loop_vars := dest
    for e in [loop_e_lower:loop_e_upper:1]i do
      let dest := loop_vars
      loop_vars ← do
        let dest ← (Elem_set dest e esize (← (FPAdd (← (Elem_read (← (D_read n)) (2 *i e) esize)) (← (Elem_read (← (D_read n)) ((2 *i e) +i 1) esize)) (← (StandardFPSCRValue ())))))
        (Elem_set dest (e +i h) esize (← (FPAdd (← (Elem_read (← (D_read m)) (2 *i e) esize)) (← (Elem_read (← (D_read m)) ((2 *i e) +i 1) esize)) (← (StandardFPSCRValue ())))))
    (pure loop_vars) ) : SailM (BitVec 64) )
  (D_set d dest)

/-- Type quantifiers: d : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VPADD_i_Op_A_txt (d : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let dest ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let h := (fdiv_int elements 2)
  let dest ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (h -i 1)
    let mut loop_vars := dest
    for e in [loop_e_lower:loop_e_upper:1]i do
      let dest := loop_vars
      loop_vars ← do
        let dest ← (Elem_set dest e esize ((← (Elem_read (← (D_read n)) (2 *i e) esize)) + (← (Elem_read (← (D_read n)) ((2 *i e) +i 1) esize))))
        (Elem_set dest (e +i h) esize ((← (Elem_read (← (D_read m)) (2 *i e) esize)) + (← (Elem_read (← (D_read m)) ((2 *i e) +i 1) esize))))
    (pure loop_vars) ) : SailM (BitVec 64) )
  (D_set d dest)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VPADDL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let h := (fdiv_int elements 2)
  let (op1, op2, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2, result) := loop_vars
      loop_vars ← do
        let (op1, op2, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (h -i 1)
          let mut loop_vars_1 := (op1, op2, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2, result) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (m +i r))) (2 *i e) esize)
              let op2 ← (Elem_read (← (D_read (m +i r))) ((2 *i e) +i 1) esize)
              let result ← (pure ((← (asl_Int op1 is_unsigned)) +i (← (asl_Int op2 is_unsigned))))
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e (2 *i esize) (integer_subrange result ((2 *i esize) -i 1) 0))))
              (pure (op1, op2, result))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize) × Int) )
        (pure (op1, op2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × Int) )
  (pure ())

/-- Type quantifiers: d : Nat, elements : Nat, esize : Nat, m : Nat, k_maximum : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VPMAX_f_Op_A_txt (d : Nat) (elements : Nat) (esize : Nat) (m : Nat) (maximum : Bool) (n : Nat) : SailM Unit := do
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let dest ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let h := (Int.ediv elements 2)
  let (dest, op1, op2) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (h -i 1)
    let mut loop_vars := (dest, op1, op2)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (dest, op1, op2) := loop_vars
      loop_vars ← do
        let op1 ← (Elem_read (← (D_read n)) (2 *i e) esize)
        let op2 ← (Elem_read (← (D_read n)) ((2 *i e) +i 1) esize)
        let dest ←
          (Elem_set dest e esize
            (← (do
              if (maximum : Bool)
              then (FPMax op1 op2 (← (StandardFPSCRValue ())))
              else (FPMin op1 op2 (← (StandardFPSCRValue ()))))))
        let op1 ← (Elem_read (← (D_read m)) (2 *i e) esize)
        let op2 ← (Elem_read (← (D_read m)) ((2 *i e) +i 1) esize)
        let dest ←
          (Elem_set dest (e +i h) esize
            (← (do
              if (maximum : Bool)
              then (FPMax op1 op2 (← (StandardFPSCRValue ())))
              else (FPMin op1 op2 (← (StandardFPSCRValue ()))))))
        (pure (dest, op1, op2))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec esize) × (BitVec esize)) )
  (D_set d dest)

/-- Type quantifiers: d : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, k_maximum : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VPMAX_i_Op_A_txt (d : Nat) (elements : Int) (esize : Nat) (m : Nat) (maximum : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let dest ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let h := (fdiv_int elements 2)
  let (dest, op1, op2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (h -i 1)
    let mut loop_vars := (dest, op1, op2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (dest, op1, op2, result) := loop_vars
      loop_vars ← do
        let op1 ← (asl_Int (← (Elem_read (← (D_read n)) (2 *i e) esize)) is_unsigned)
        let op2 ← (asl_Int (← (Elem_read (← (D_read n)) ((2 *i e) +i 1) esize)) is_unsigned)
        let result : Int :=
          if (maximum : Bool)
          then (Max.max op1 op2)
          else (Min.min op1 op2)
        let dest ← (Elem_set dest e esize (integer_subrange result (esize -i 1) 0))
        let op1 ← (asl_Int (← (Elem_read (← (D_read m)) (2 *i e) esize)) is_unsigned)
        let op2 ← (asl_Int (← (Elem_read (← (D_read m)) ((2 *i e) +i 1) esize)) is_unsigned)
        let result : Int :=
          if (maximum : Bool)
          then (Max.max op1 op2)
          else (Min.min op1 op2)
        let dest ← (Elem_set dest (e +i h) esize (integer_subrange result (esize -i 1) 0))
        (pure (dest, op1, op2, result))
    (pure loop_vars) ) : SailM ((BitVec 64) × Int × Int × Int) )
  (D_set d dest)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQABS_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let result ← (pure (Int.natAbs (BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize)))))
            let sat ← (( do (undefined_bool ()) ) : SailM Bool )
            let sat ← (( do
              let (__tup_0, __tup_1) ← do (SignedSatQ result esize)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize __tup_0)))
              (pure __tup_1) ) : SailM Bool )
            if (sat : Bool)
            then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
            else (pure ())
            (pure result)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQADD_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let sum ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let sum ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := sum
    for r in [loop_r_lower:loop_r_upper:1]i do
      let sum := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := sum
        for e in [loop_e_lower:loop_e_upper:1]i do
          let sum := loop_vars_1
          loop_vars_1 ← do
            let sum ← (pure ((← (asl_Int (← (Elem_read (← (D_read (n +i r))) e esize)) is_unsigned)) +i (← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned))))
            let sat ← (( do (undefined_bool ()) ) : SailM Bool )
            let sat ← (( do
              let (__tup_0, __tup_1) ← do (SatQ sum esize is_unsigned)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize __tup_0)))
              (pure __tup_1) ) : SailM Bool )
            if (sat : Bool)
            then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
            else (pure ())
            (pure sum)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: k_add : Bool, d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, k_scalar_form : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQDMLAL_Op_A_txt (add : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let sat1 ← (( do (undefined_bool ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do
    if (scalar_form : Bool)
    then (do (pure (BitVec.toInt (← (Elem_read (← (Din_read m)) index esize)))))
    else (pure op2) ) : SailM Int )
  let (op1, op2, product, sat1) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (op1, op2, product, sat1)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (op1, op2, product, sat1) := loop_vars
      loop_vars ← do
        let op2 ← (( do
          if ((! scalar_form) : Bool)
          then (do (pure (BitVec.toInt (← (Elem_read (← (Din_read m)) e esize)))))
          else (pure op2) ) : SailM Int )
        let op1 ← (pure (BitVec.toInt (← (Elem_read (← (Din_read n)) e esize))))
        let (product, sat1) ← (( do
          let (tup__0, tup__1) ← do (SignedSatQ ((2 *i op1) *i op2) (2 *i esize))
          let product : (BitVec (2 * esize)) := tup__0
          let sat1 : Bool := tup__1
          (pure (product, sat1)) ) : SailM ((BitVec (2 * esize)) × Bool) )
        let result ← (( do (undefined_int ()) ) : SailM Int )
        let result ← (( do
          if (add : Bool)
          then (do (pure ((BitVec.toInt (← (Elem_read (← (Qin_read (Int.shiftr d 1))) e (2 *i esize)))) +i (BitVec.toInt product))))
          else (do (pure ((BitVec.toInt (← (Elem_read (← (Qin_read (Int.shiftr d 1))) e (2 *i esize)))) -i (BitVec.toInt product)))) ) : SailM Int )
        let result := result
        let sat2 ← (( do (undefined_bool ()) ) : SailM Bool )
        let sat2 ← (( do
          let (__tup_0, __tup_1) ← do (SignedSatQ result (2 *i esize))
          (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) __tup_0)))
          (pure __tup_1) ) : SailM Bool )
        if ((sat1 || sat2) : Bool)
        then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
        else (pure ())
        (pure (op1, op2, product, sat1))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec (2 * esize)) × Bool) )
  (pure ())

/-- Type quantifiers: k_add : Bool, d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, k_scalar_form : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQDMLSL_Op_A_txt (add : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let sat1 ← (( do (undefined_bool ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do
    if (scalar_form : Bool)
    then (do (pure (BitVec.toInt (← (Elem_read (← (Din_read m)) index esize)))))
    else (pure op2) ) : SailM Int )
  let (op1, op2, product, sat1) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (op1, op2, product, sat1)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (op1, op2, product, sat1) := loop_vars
      loop_vars ← do
        let op2 ← (( do
          if ((! scalar_form) : Bool)
          then (do (pure (BitVec.toInt (← (Elem_read (← (Din_read m)) e esize)))))
          else (pure op2) ) : SailM Int )
        let op1 ← (pure (BitVec.toInt (← (Elem_read (← (Din_read n)) e esize))))
        let (product, sat1) ← (( do
          let (tup__0, tup__1) ← do (SignedSatQ ((2 *i op1) *i op2) (2 *i esize))
          let product : (BitVec (2 * esize)) := tup__0
          let sat1 : Bool := tup__1
          (pure (product, sat1)) ) : SailM ((BitVec (2 * esize)) × Bool) )
        let result ← (( do (undefined_int ()) ) : SailM Int )
        let result ← (( do
          if (add : Bool)
          then (do (pure ((BitVec.toInt (← (Elem_read (← (Qin_read (Int.shiftr d 1))) e (2 *i esize)))) +i (BitVec.toInt product))))
          else (do (pure ((BitVec.toInt (← (Elem_read (← (Qin_read (Int.shiftr d 1))) e (2 *i esize)))) -i (BitVec.toInt product)))) ) : SailM Int )
        let result := result
        let sat2 ← (( do (undefined_bool ()) ) : SailM Bool )
        let sat2 ← (( do
          let (__tup_0, __tup_1) ← do (SignedSatQ result (2 *i esize))
          (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) __tup_0)))
          (pure __tup_1) ) : SailM Bool )
        if ((sat1 || sat2) : Bool)
        then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
        else (pure ())
        (pure (op1, op2, product, sat1))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec (2 * esize)) × Bool) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, regs : Nat, k_scalar_form : Bool, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQDMULH_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (regs : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do
    if (scalar_form : Bool)
    then (do (pure (BitVec.toInt (← (Elem_read (← (D_read m)) index esize)))))
    else (pure op2) ) : SailM Int )
  let (op1, op2, result, sat) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2, result, sat)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2, result, sat) := loop_vars
      loop_vars ← do
        let (op1, op2, result, sat) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2, result, sat)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2, result, sat) := loop_vars_1
            loop_vars_1 ← do
              let op2 ← (( do
                if ((! scalar_form) : Bool)
                then (do (pure (BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize)))))
                else (pure op2) ) : SailM Int )
              let op1 ← (pure (BitVec.toInt (← (Elem_read (← (D_read (n +i r))) e esize))))
              let (result, sat) ← (( do
                let (tup__0, tup__1) ← do (SignedSatQ (Int.shiftr ((2 *i op1) *i op2) esize) esize)
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                (pure (result, sat)) ) : SailM ((BitVec esize) × Bool) )
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              if (sat : Bool)
              then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
              else (pure ())
              (pure (op1, op2, result, sat))
          (pure loop_vars_1) ) : SailM (Int × Int × (BitVec esize) × Bool) )
        (pure (op1, op2, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec esize) × Bool) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, k_scalar_form : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQDMULL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do
    if (scalar_form : Bool)
    then (do (pure (BitVec.toInt (← (Elem_read (← (Din_read m)) index esize)))))
    else (pure op2) ) : SailM Int )
  let (op1, op2, product, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (op1, op2, product, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (op1, op2, product, sat) := loop_vars
      loop_vars ← do
        let op2 ← (( do
          if ((! scalar_form) : Bool)
          then (do (pure (BitVec.toInt (← (Elem_read (← (Din_read m)) e esize)))))
          else (pure op2) ) : SailM Int )
        let op1 ← (pure (BitVec.toInt (← (Elem_read (← (Din_read n)) e esize))))
        let (product, sat) ← (( do
          let (tup__0, tup__1) ← do (SignedSatQ ((2 *i op1) *i op2) (2 *i esize))
          let product : (BitVec (2 * esize)) := tup__0
          let sat : Bool := tup__1
          (pure (product, sat)) ) : SailM ((BitVec (2 * esize)) × Bool) )
        (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) product)))
        if (sat : Bool)
        then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
        else (pure ())
        (pure (op1, op2, product, sat))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec (2 * esize)) × Bool) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, k_dest_unsigned : Bool, elements : Int, esize : Nat, m : Nat, k_src_unsigned : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQMOVN_Op_A_txt (d__arg : Nat) (dest_unsigned : Bool) (elements : Int) (esize : Nat) (m : Nat) (src_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let operand ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let operand ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := operand
    for e in [loop_e_lower:loop_e_upper:1]i do
      let operand := loop_vars
      loop_vars ← do
        let operand ← (asl_Int (← (Elem_read (← (Qin_read (Int.shiftr m 1))) e (2 *i esize))) src_unsigned)
        let sat ← (( do (undefined_bool ()) ) : SailM Bool )
        let sat ← (( do
          let (__tup_0, __tup_1) ← do (SatQ operand esize dest_unsigned)
          (D_set d (← (Elem_set (← (D_read d)) e esize __tup_0)))
          (pure __tup_1) ) : SailM Bool )
        if (sat : Bool)
        then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
        else (pure ())
        (pure operand)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQNEG_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let result ← (pure (Neg.neg (BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize)))))
            let sat ← (( do (undefined_bool ()) ) : SailM Bool )
            let sat ← (( do
              let (__tup_0, __tup_1) ← do (SignedSatQ result esize)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize __tup_0)))
              (pure __tup_1) ) : SailM Bool )
            if (sat : Bool)
            then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
            else (pure ())
            (pure result)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, regs : Nat, k_scalar_form : Bool, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQRDMULH_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (regs : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let round : Bool := true
  let op2 ← (( do
    if (scalar_form : Bool)
    then (do (pure (BitVec.toInt (← (Elem_read (← (D_read m)) index esize)))))
    else (pure op2) ) : SailM Int )
  let (op1, op2, result, sat) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2, result, sat)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2, result, sat) := loop_vars
      loop_vars ← do
        let (op1, op2, result, sat) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2, result, sat)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2, result, sat) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (pure (BitVec.toInt (← (Elem_read (← (D_read (n +i r))) e esize))))
              let op2 ← (( do
                if ((! scalar_form) : Bool)
                then (do (pure (BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize)))))
                else (pure op2) ) : SailM Int )
              let rdmulh ← do (RShr ((2 *i op1) *i op2) esize round)
              let (result, sat) ← (( do
                let (tup__0, tup__1) ← do (SignedSatQ rdmulh esize)
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                (pure (result, sat)) ) : SailM ((BitVec esize) × Bool) )
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              if (sat : Bool)
              then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
              else (pure ())
              (pure (op1, op2, result, sat))
          (pure loop_vars_1) ) : SailM (Int × Int × (BitVec esize) × Bool) )
        (pure (op1, op2, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec esize) × Bool) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, regs : Nat, k_scalar_form : Bool, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQRDMLAH_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (regs : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let op3 ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let round : Bool := true
  let op2 ← (( do
    if (scalar_form : Bool)
    then (do (pure (BitVec.toInt (← (Elem_read (← (D_read m)) index esize)))))
    else (pure op2) ) : SailM Int )
  let (op1, op2, op3, result, sat) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2, op3, result, sat)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2, op3, result, sat) := loop_vars
      loop_vars ← do
        let (op1, op2, op3, result, sat) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2, op3, result, sat)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2, op3, result, sat) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (pure (BitVec.toInt (← (Elem_read (← (D_read (n +i r))) e esize))))
              let op3 ← (pure (Int.shiftl (BitVec.toInt (← (Elem_read (← (D_read (d +i r))) e esize))) esize))
              let op2 ← (( do
                if ((! scalar_form) : Bool)
                then (do (pure (BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize)))))
                else (pure op2) ) : SailM Int )
              let rdmlah ← do (RShr (op3 +i (2 *i (op1 *i op2))) esize round)
              let (result, sat) ← (( do
                let (tup__0, tup__1) ← do (SignedSatQ rdmlah esize)
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                (pure (result, sat)) ) : SailM ((BitVec esize) × Bool) )
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              if (sat : Bool)
              then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
              else (pure ())
              (pure (op1, op2, op3, result, sat))
          (pure loop_vars_1) ) : SailM (Int × Int × Int × (BitVec esize) × Bool) )
        (pure (op1, op2, op3, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × Int × (BitVec esize) × Bool) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, regs : Nat, k_scalar_form : Bool, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQRDMLSH_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (regs : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let op3 ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let round : Bool := true
  let op2 ← (( do
    if (scalar_form : Bool)
    then (do (pure (BitVec.toInt (← (Elem_read (← (D_read m)) index esize)))))
    else (pure op2) ) : SailM Int )
  let (op1, op2, op3, result, sat) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2, op3, result, sat)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2, op3, result, sat) := loop_vars
      loop_vars ← do
        let (op1, op2, op3, result, sat) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2, op3, result, sat)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2, op3, result, sat) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (pure (BitVec.toInt (← (Elem_read (← (D_read (n +i r))) e esize))))
              let op3 ← (pure (Int.shiftl (BitVec.toInt (← (Elem_read (← (D_read (d +i r))) e esize))) esize))
              let op2 ← (( do
                if ((! scalar_form) : Bool)
                then (do (pure (BitVec.toInt (← (Elem_read (← (D_read (m +i r))) e esize)))))
                else (pure op2) ) : SailM Int )
              let rdmlsh ← do (RShr (op3 -i (2 *i (op1 *i op2))) esize round)
              let (result, sat) ← (( do
                let (tup__0, tup__1) ← do (SignedSatQ rdmlsh esize)
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                (pure (result, sat)) ) : SailM ((BitVec esize) × Bool) )
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              if (sat : Bool)
              then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
              else (pure ())
              (pure (op1, op2, op3, result, sat))
          (pure loop_vars_1) ) : SailM (Int × Int × Int × (BitVec esize) × Bool) )
        (pure (op1, op2, op3, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × Int × (BitVec esize) × Bool) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQRSHL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (result, sat) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (result, sat)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, sat) := loop_vars
      loop_vars ← do
        let (result, sat) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (result, sat)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (result, sat) := loop_vars_1
            loop_vars_1 ← do
              let element ← (( do (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned) ) : SailM Int )
              let shift ← (( do (pure (BitVec.toInt (Sail.BitVec.extractLsb (← (Elem_read (← (D_read (n +i r))) e esize)) 7 0))) ) : SailM Int )
              let element : Int :=
                if ((shift ≥b 0) : Bool)
                then (_shl_int_general element shift)
                else
                  (let shift := (Neg.neg shift)
                  (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
              let element := element
              let (result, sat) ← (( do
                let (tup__0, tup__1) ← do (SatQ element esize is_unsigned)
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                (pure (result, sat)) ) : SailM ((BitVec esize) × Bool) )
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              if (sat : Bool)
              then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
              else (pure ())
              (pure (result, sat))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × Bool) )
        (pure (result, sat))
    (pure loop_vars) ) : SailM ((BitVec esize) × Bool) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, k_dest_unsigned : Bool, elements : Nat, esize : Nat, m : Nat, shift_amount : Int, k_src_unsigned : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQRSHRN_Op_A_txt (d__arg : Nat) (dest_unsigned : Bool) (elements : Nat) (esize : Nat) (m : Nat) (shift_amount : Int) (src_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let operand ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let (operand, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (operand, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (operand, result, sat) := loop_vars
      loop_vars ← do
        let operand ← (asl_Int (← (Elem_read (← (Qin_read (Int.shiftr m 1))) e (2 *i esize))) src_unsigned)
        let rshrn ← do (RShr operand shift_amount round)
        let (result, sat) ← (( do
          let (tup__0, tup__1) ← do (SatQ rshrn esize dest_unsigned)
          let result : (BitVec esize) := tup__0
          let sat : Bool := tup__1
          (pure (result, sat)) ) : SailM ((BitVec esize) × Bool) )
        (D_set d (← (Elem_set (← (D_read d)) e esize result)))
        if (sat : Bool)
        then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
        else (pure ())
        (pure (operand, result, sat))
    (pure loop_vars) ) : SailM (Int × (BitVec esize) × Bool) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, k_dest_unsigned : Bool, elements : Nat, esize : Nat, m : Nat, regs : Nat, shift_amount : Int, k_src_unsigned : Bool, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQSHL_i_Op_A_txt (d__arg : Nat) (dest_unsigned : Bool) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) (src_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let operand ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let (operand, result, sat) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (operand, result, sat)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (operand, result, sat) := loop_vars
      loop_vars ← do
        let (operand, result, sat) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (operand, result, sat)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (operand, result, sat) := loop_vars_1
            loop_vars_1 ← do
              let operand ← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) src_unsigned)
              let (result, sat) ← (( do
                let (tup__0, tup__1) ← do (SatQ (_shl_int_general operand shift_amount) esize dest_unsigned)
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                (pure (result, sat)) ) : SailM ((BitVec esize) × Bool) )
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              if (sat : Bool)
              then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
              else (pure ())
              (pure (operand, result, sat))
          (pure loop_vars_1) ) : SailM (Int × (BitVec esize) × Bool) )
        (pure (operand, result, sat))
    (pure loop_vars) ) : SailM (Int × (BitVec esize) × Bool) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQSHL_r_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let operand ← (( do (undefined_int ()) ) : SailM Int )
  let shift ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let (operand, shift) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (operand, shift)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (operand, shift) := loop_vars
      loop_vars ← do
        let (operand, shift) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (operand, shift)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (operand, shift) := loop_vars_1
            loop_vars_1 ← do
              let shift ← (pure (BitVec.toInt (Sail.BitVec.extractLsb (← (Elem_read (← (D_read (n +i r))) e esize)) 7 0)))
              let operand ← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)
              let sat ← (( do (undefined_bool ()) ) : SailM Bool )
              let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let (result, sat) ← (( do
                if ((shift ≥b 0) : Bool)
                then
                  (do
                    let (tup__0, tup__1) ← do (SatQ (_shl_int_general operand shift) esize is_unsigned)
                    let result : (BitVec esize) := tup__0
                    let sat : Bool := tup__1
                    (pure (result, sat)))
                else
                  (do
                    let (tup__0, tup__1) ← do (SatQ (_shr_int_general operand (Neg.neg shift)) esize is_unsigned)
                    let result : (BitVec esize) := tup__0
                    let sat : Bool := tup__1
                    (pure (result, sat))) ) : SailM ((BitVec esize) × Bool) )
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              if (sat : Bool)
              then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
              else (pure ())
              (pure (operand, shift))
          (pure loop_vars_1) ) : SailM (Int × Int) )
        (pure (operand, shift))
    (pure loop_vars) ) : SailM (Int × Int) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, k_dest_unsigned : Bool, elements : Nat, esize : Nat, m : Nat, shift_amount : Int, k_src_unsigned : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQSHRN_Op_A_txt (d__arg : Nat) (dest_unsigned : Bool) (elements : Nat) (esize : Nat) (m : Nat) (shift_amount : Int) (src_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let operand ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let (operand, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (operand, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (operand, result, sat) := loop_vars
      loop_vars ← do
        let operand ← (asl_Int (← (Elem_read (← (Qin_read (Int.shiftr m 1))) e (2 *i esize))) src_unsigned)
        let (result, sat) ← (( do
          let (tup__0, tup__1) ← do (SatQ (_shr_int_general operand shift_amount) esize dest_unsigned)
          let result : (BitVec esize) := tup__0
          let sat : Bool := tup__1
          (pure (result, sat)) ) : SailM ((BitVec esize) × Bool) )
        (D_set d (← (Elem_set (← (D_read d)) e esize result)))
        if (sat : Bool)
        then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
        else (pure ())
        (pure (operand, result, sat))
    (pure loop_vars) ) : SailM (Int × (BitVec esize) × Bool) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQSUB_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let diff ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let diff ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := diff
    for r in [loop_r_lower:loop_r_upper:1]i do
      let diff := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := diff
        for e in [loop_e_lower:loop_e_upper:1]i do
          let diff := loop_vars_1
          loop_vars_1 ← do
            let diff ← (pure ((← (asl_Int (← (Elem_read (← (D_read (n +i r))) e esize)) is_unsigned)) -i (← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned))))
            let sat ← (( do (undefined_bool ()) ) : SailM Bool )
            let sat ← (( do
              let (__tup_0, __tup_1) ← do (SatQ diff esize is_unsigned)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize __tup_0)))
              (pure __tup_1) ) : SailM Bool )
            if (sat : Bool)
            then (FPSCR_write (_update_FPSCR_Type_QC (← (FPSCR_read__1 ())) 1#1))
            else (pure ())
            (pure diff)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRADDHN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (RShr (BitVec.toNat ((← (Elem_read (← (Qin_read (Int.shiftr n 1))) e (2 *i esize))) + (← (Elem_read (← (Qin_read (Int.shiftr m 1))) e (2 *i esize))))) esize round)
        (D_set d (← (Elem_set (← (D_read d)) e esize (integer_subrange result (esize -i 1) 0))))
        (pure result)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_floating_point : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRECPE_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          if (floating_point : Bool)
          then (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPRecipEstimate (← (Elem_read (← (D_read (m +i r))) e esize)) (← (StandardFPSCRValue ())))))))
          else
            (do
              sail_assert (esize == 32) "src/instrs32.sail:34614.47-34614.48"
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (UnsignedRecipEstimate (← (Elem_read (← (D_read (m +i r))) e esize))))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRECPS_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPRecipStep (← (Elem_read (← (D_read (n +i r))) e esize)) (← (Elem_read (← (D_read (m +i r))) e esize)))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: containers : Int, d : Nat, elements_per_container : Int, esize : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VREV16_Op_A_txt (containers : Int) (d : Nat) (elements_per_container : Int) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let rev_element ← (( do (undefined_int ()) ) : SailM Int )
  let (element, result, rev_element) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (element, result, rev_element)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (element, result, rev_element) := loop_vars
      loop_vars ← do
        let element : Int := 0
        let (element, result, rev_element) ← (( do
          let loop_c_lower := 0
          let loop_c_upper := (containers -i 1)
          let mut loop_vars_1 := (element, result, rev_element)
          for c in [loop_c_lower:loop_c_upper:1]i do
            let (element, result, rev_element) := loop_vars_1
            loop_vars_1 ← do
              let rev_element : Int := ((element +i elements_per_container) -i 1)
              let (element, result, rev_element) ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements_per_container -i 1)
                let mut loop_vars_2 := (element, result, rev_element)
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let (element, result, rev_element) := loop_vars_2
                  loop_vars_2 ← do
                    let result ← (( do
                      let rev_element := rev_element
                      let element := element
                      (Elem_set result rev_element esize (← (Elem_read (← (D_read (m +i r))) element esize))) ) : SailM (BitVec 64) )
                    let element : Int := (element +i 1)
                    let rev_element : Int := (rev_element -i 1)
                    (pure (element, result, rev_element))
                (pure loop_vars_2) ) : SailM (Int × (BitVec 64) × Int) )
              (pure (element, result, rev_element))
          (pure loop_vars_1) ) : SailM (Int × (BitVec 64) × Int) )
        (D_set (d +i r) result)
        (pure (element, result, rev_element))
    (pure loop_vars) ) : SailM (Int × (BitVec 64) × Int) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRHADD_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let (op1, op2, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, op2, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, op2, result) := loop_vars
      loop_vars ← do
        let (op1, op2, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, op2, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, op2, result) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (asl_Int (← (Elem_read (← (D_read (n +i r))) e esize)) is_unsigned)
              let op2 ← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)
              let result : Int := (Int.shiftr ((op1 +i op2) +i 1) 1)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange result (esize -i 1) 0))))
              (pure (op1, op2, result))
          (pure loop_vars_1) ) : SailM (Int × Int × Int) )
        (pure (op1, op2, result))
    (pure loop_vars) ) : SailM (Int × Int × Int) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSHL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← do (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)
            let shift ← (( do (pure (BitVec.toInt (Sail.BitVec.extractLsb (← (Elem_read (← (D_read (n +i r))) e esize)) 7 0))) ) : SailM Int )
            let result : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
            (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange result (esize -i 1) 0))))
            (pure result)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs : Nat, shift_amount : Int, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSHR_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let result ← (RShr (← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)) shift_amount round)
            (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange result (esize -i 1) 0))))
            (pure result)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, shift_amount : Int, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSHRN_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (shift_amount : Int) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (RShr (BitVec.toNat (← (Elem_read (← (Qin_read (Int.shiftr m 1))) e (2 *i esize)))) shift_amount round)
        (D_set d (← (Elem_set (← (D_read d)) e esize (integer_subrange result (esize -i 1) 0))))
        (pure result)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_floating_point : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSQRTE_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          if (floating_point : Bool)
          then (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPRSqrtEstimate (← (Elem_read (← (D_read (m +i r))) e esize)) (← (StandardFPSCRValue ())))))))
          else
            (do
              sail_assert (esize == 32) "src/instrs32.sail:35439.47-35439.48"
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (UnsignedRSqrtEstimate (← (Elem_read (← (D_read (m +i r))) e esize))))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSQRTS_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPRSqrtStep (← (Elem_read (← (D_read (n +i r))) e esize)) (← (Elem_read (← (D_read (m +i r))) e esize)))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs : Nat, shift_amount : Int, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSRA_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let result ← (RShr (← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)) shift_amount round)
            (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (BitVec.addInt (← (Elem_read (← (D_read (d +i r))) e esize)) result))))
            (pure result)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSUBHN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (RShr (BitVec.toNat ((← (Elem_read (← (Qin_read (Int.shiftr n 1))) e (2 *i esize))) - (← (Elem_read (← (Qin_read (Int.shiftr m 1))) e (2 *i esize))))) esize round)
        (D_set d (← (Elem_set (← (D_read d)) e esize (integer_subrange result (esize -i 1) 0))))
        (pure result)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, regs : Nat, shift_amount : Int, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSHL_i_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize ((← (Elem_read (← (D_read (m +i r))) e esize)) <<< shift_amount))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, shift_amount : Int, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSHLL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (shift_amount : Int) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (pure (_shl_int_general (← (asl_Int (← (Elem_read (← (Din_read m)) e esize)) is_unsigned)) shift_amount))
        (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) (integer_subrange result ((2 *i esize) -i 1) 0))))
        (pure result)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSHL_r_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let shift ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let shift ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := shift
    for r in [loop_r_lower:loop_r_upper:1]i do
      let shift := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := shift
        for e in [loop_e_lower:loop_e_upper:1]i do
          let shift := loop_vars_1
          loop_vars_1 ← do
            let shift ← (pure (BitVec.toInt (Sail.BitVec.extractLsb (← (Elem_read (← (D_read (n +i r))) e esize)) 7 0)))
            let result ← (( do (undefined_int ()) ) : SailM Int )
            let result ← (( do
              if ((shift ≥b 0) : Bool)
              then (do (pure (_shl_int_general (← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)) shift)))
              else (do (pure (_shr_int_general (← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)) (Neg.neg shift)))) ) : SailM Int )
            let result := result
            (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange result (esize -i 1) 0))))
            (pure shift)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs : Nat, shift_amount : Int, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSHR_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let result ← (pure (_shr_int_general (← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)) shift_amount))
            (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (integer_subrange result (esize -i 1) 0))))
            (pure result)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, shift_amount : Int, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSHRN_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (shift_amount : Int) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (pure ((← (Elem_read (← (Qin_read (Int.shiftr m 1))) e (2 *i esize))) >>> shift_amount))
        (D_set d (← (Elem_set (← (D_read d)) e esize (Sail.BitVec.extractLsb result (esize -i 1) 0))))
        (pure result)
    (pure loop_vars) ) : SailM (BitVec (2 * esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, regs : Nat, shift_amount : Int, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSLI_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) : SailM Unit := do
  let d : Int := d__arg
  let shifted_op ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let mask : (BitVec esize) := ((Ones (n := esize)) <<< shift_amount)
  let shifted_op ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := shifted_op
    for r in [loop_r_lower:loop_r_upper:1]i do
      let shifted_op := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := shifted_op
        for e in [loop_e_lower:loop_e_upper:1]i do
          let shifted_op := loop_vars_1
          loop_vars_1 ← do
            let shifted_op ← (pure ((← (Elem_read (← (D_read (m +i r))) e esize)) <<< shift_amount))
            (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (((← (Elem_read (← (D_read (d +i r))) e esize)) &&& (Complement.complement mask)) ||| shifted_op))))
            (pure shifted_op)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec esize) )
  (pure ())

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VSQRT_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 => (S_set d ((Zeros (n := 16)) +++ (← (FPSqrt (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ()))))))
  | 32 => (S_set d (← (FPSqrt (← (S_read m)) (← (FPSCR_read ())))))
  | 64 => (D_set d (← (FPSqrt (← (D_read m)) (← (FPSCR_read ())))))
  | _ => (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs : Nat, shift_amount : Int, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSRA_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let result ← (pure (_shr_int_general (← (asl_Int (← (Elem_read (← (D_read (m +i r))) e esize)) is_unsigned)) shift_amount))
            (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (BitVec.addInt (← (Elem_read (← (D_read (d +i r))) e esize)) result))))
            (pure result)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, regs : Nat, shift_amount : Int, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSRI_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) : SailM Unit := do
  let d : Int := d__arg
  let shifted_op ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let mask : (BitVec esize) := ((Ones (n := esize)) >>> shift_amount)
  let shifted_op ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := shifted_op
    for r in [loop_r_lower:loop_r_upper:1]i do
      let shifted_op := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := shifted_op
        for e in [loop_e_lower:loop_e_upper:1]i do
          let shifted_op := loop_vars_1
          loop_vars_1 ← do
            let shifted_op ← (pure ((← (Elem_read (← (D_read (m +i r))) e esize)) >>> shift_amount))
            (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (((← (Elem_read (← (D_read (d +i r))) e esize)) &&& (Complement.complement mask)) ||| shifted_op))))
            (pure shifted_op)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec esize) )
  (pure ())

/-- Type quantifiers: alignment : Nat, d : Nat, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem ebytes [1, 2, 4] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 2, 4] -/
def execute_aarch32_instrs_VST1_1_Op_A_txt (alignment : Nat) (d : Nat) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  (MemU_set address ebytes (← (Elem_read (← (D_read d)) index (8 *i ebytes))))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) ebytes)))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d : Nat, ebytes : Nat, elements : Int, m : Nat, n : Nat, k_register_index : Bool, regs : Nat, k_wback : Bool, List.elem regs [1, 2, 3, 4] ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VST1_m_Op_A_txt (alignment : Nat) (d : Nat) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (regs : Nat) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let address ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := address
    for r in [loop_r_lower:loop_r_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := address
        for e in [loop_e_lower:loop_e_upper:1]i do
          let address := loop_vars_1
          loop_vars_1 ← do
            if ((ebytes != 8) : Bool)
            then (MemU_set address ebytes (← (Elem_read (← (D_read (d +i r))) e (8 *i ebytes))))
            else
              (do
                if ((←((pure (! (IsAligned__1 address ebytes))) <&&> (do
                     (AlignmentEnforced ())))) : Bool)
                then (AArch32_Abort address (← (AlignmentFault accdesc)))
                else (pure ())
                let data ← (( do (Elem_read (← (D_read (d +i r))) e 64) ) : SailM (BitVec 64) )
                if ((← (BigEndian AccessType_ASIMD)) : Bool)
                then
                  (do
                    (MemU_set address 4 (Sail.BitVec.extractLsb data 63 32))
                    (MemU_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb data 31 0)))
                else
                  (do
                    (MemU_set address 4 (Sail.BitVec.extractLsb data 31 0))
                    (MemU_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb data 63 32))))
            (pure (BitVec.addInt address ebytes))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (8 *i regs))))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem ebytes [1, 2, 4] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 2, 4, 8] -/
def execute_aarch32_instrs_VST2_1_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  (MemU_set address ebytes (← (Elem_read (← (D_read d)) index (8 *i ebytes))))
  (MemU_set (BitVec.addInt address ebytes) ebytes (← (Elem_read (← (D_read d2)) index (8 *i ebytes))))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (2 *i ebytes))))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, ebytes : Nat, elements : Int, m : Nat, n : Nat, pairs : Nat, k_register_index : Bool, k_wback : Bool, List.elem pairs [1, 2] ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VST2_m_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (pairs : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let address ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (pairs -i 1)
    let mut loop_vars := address
    for r in [loop_r_lower:loop_r_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := address
        for e in [loop_e_lower:loop_e_upper:1]i do
          let address := loop_vars_1
          loop_vars_1 ← do
            (MemU_set address ebytes (← (Elem_read (← (D_read (d +i r))) e (8 *i ebytes))))
            (MemU_set (BitVec.addInt address ebytes) ebytes (← (Elem_read (← (D_read (d2 +i r))) e (8 *i ebytes))))
            (pure (BitVec.addInt address (2 *i ebytes)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (16 *i pairs))))
  else (pure ())

/-- Type quantifiers: d : Nat, d2 : Int, d3 : Int, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem ebytes [1, 2, 4] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VST3_1_Op_A_txt (d : Nat) (d2 : Int) (d3 : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (MemU_set address ebytes (← (Elem_read (← (D_read d)) index (8 *i ebytes))))
  (MemU_set (BitVec.addInt address ebytes) ebytes (← (Elem_read (← (D_read d2)) index (8 *i ebytes))))
  (MemU_set (BitVec.addInt address (2 *i ebytes)) ebytes (← (Elem_read (← (D_read d3)) index (8 *i ebytes))))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (3 *i ebytes))))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, d3 : Int, ebytes : Nat, elements : Int, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 8] -/
def execute_aarch32_instrs_VST3_m_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (d3 : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let address ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := address
    for e in [loop_e_lower:loop_e_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        (MemU_set address ebytes (← (Elem_read (← (D_read d)) e (8 *i ebytes))))
        (MemU_set (BitVec.addInt address ebytes) ebytes (← (Elem_read (← (D_read d2)) e (8 *i ebytes))))
        (MemU_set (BitVec.addInt address (2 *i ebytes)) ebytes (← (Elem_read (← (D_read d3)) e (8 *i ebytes))))
        (pure (BitVec.addInt address (3 *i ebytes)))
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) 24)))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, d3 : Int, d4 : Int, ebytes : Nat, index : Nat, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem ebytes [1, 2, 4] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VST4_1_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (d3 : Int) (d4 : Int) (ebytes : Nat) (index : Nat) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  (MemU_set address ebytes (← (Elem_read (← (D_read d)) index (8 *i ebytes))))
  (MemU_set (BitVec.addInt address ebytes) ebytes (← (Elem_read (← (D_read d2)) index (8 *i ebytes))))
  (MemU_set (BitVec.addInt address (2 *i ebytes)) ebytes (← (Elem_read (← (D_read d3)) index (8 *i ebytes))))
  (MemU_set (BitVec.addInt address (3 *i ebytes)) ebytes (← (Elem_read (← (D_read d4)) index (8 *i ebytes))))
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) (4 *i ebytes))))
  else (pure ())

/-- Type quantifiers: alignment : Nat, d : Nat, d2 : Int, d3 : Int, d4 : Int, ebytes : Nat, elements : Int, m : Nat, n : Nat, k_register_index : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem ebytes [1, 2, 4, 8] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem alignment [1, 4, 8, 16, 32] -/
def execute_aarch32_instrs_VST4_m_Op_A_txt (alignment : Nat) (d : Nat) (d2 : Int) (d3 : Int) (d4 : Int) (ebytes : Nat) (elements : Int) (m : Nat) (n : Nat) (register_index : Bool) (wback : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let nontemporal : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescASIMD MemOp_STORE nontemporal tagchecked) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address alignment)) : Bool)
  then (AArch32_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let address ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := address
    for e in [loop_e_lower:loop_e_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        (MemU_set address ebytes (← (Elem_read (← (D_read d)) e (8 *i ebytes))))
        (MemU_set (BitVec.addInt address ebytes) ebytes (← (Elem_read (← (D_read d2)) e (8 *i ebytes))))
        (MemU_set (BitVec.addInt address (2 *i ebytes)) ebytes (← (Elem_read (← (D_read d3)) e (8 *i ebytes))))
        (MemU_set (BitVec.addInt address (3 *i ebytes)) ebytes (← (Elem_read (← (D_read d4)) e (8 *i ebytes))))
        (pure (BitVec.addInt address (4 *i ebytes)))
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      if (register_index : Bool)
      then (R_set n ((← (R_read n)) + (← (R_read m))))
      else (R_set n (BitVec.addInt (← (R_read n)) 32)))
  else (pure ())

/-- Type quantifiers: k_add : Bool, d : Nat, n : Nat, regs : Int, k_single_regs : Bool, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VSTM_Op_A_txt (add : Bool) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (regs : Int) (single_regs : Bool) (wback : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  let address ← (( do
    if (add : Bool)
    then (R_read n)
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := address
    for r in [loop_r_lower:loop_r_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        if (single_regs : Bool)
        then
          (do
            (MemA_set address 4 (← (S_read (d +i r))))
            (pure (BitVec.addInt address 4)))
        else
          (do
            if ((← (BigEndian AccessType_ASIMD)) : Bool)
            then
              (do
                (MemA_set address 4 (Sail.BitVec.extractLsb (← (D_read (d +i r))) 63 32))
                (MemA_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb (← (D_read (d +i r))) 31 0)))
            else
              (do
                (MemA_set address 4 (Sail.BitVec.extractLsb (← (D_read (d +i r))) 31 0))
                (MemA_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb (← (D_read (d +i r))) 63 32)))
            (pure (BitVec.addInt address 8)))
    (pure loop_vars) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (R_set n
      (← (do
        if (add : Bool)
        then (pure ((← (R_read n)) + imm32))
        else (pure ((← (R_read n)) - imm32)))))
  else (pure ())

/-- Type quantifiers: k_add : Bool, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VSTR_Op_A_txt (add : Bool) (d : Nat) (esize : Nat) (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  let address ← (( do
    if (add : Bool)
    then (pure ((← (R_read n)) + imm32))
    else (pure ((← (R_read n)) - imm32)) ) : SailM (BitVec 32) )
  match esize with
  | 16 => (MemA_set address 2 (Sail.BitVec.extractLsb (← (S_read d)) 15 0))
  | 32 => (MemA_set address 4 (← (S_read d)))
  | 64 =>
    (do
      if ((← (BigEndian AccessType_ASIMD)) : Bool)
      then
        (do
          (MemA_set address 4 (Sail.BitVec.extractLsb (← (D_read d)) 63 32))
          (MemA_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb (← (D_read d)) 31 0)))
      else
        (do
          (MemA_set address 4 (Sail.BitVec.extractLsb (← (D_read d)) 31 0))
          (MemA_set (BitVec.addInt address 4) 4 (Sail.BitVec.extractLsb (← (D_read d)) 63 32))))
  | _ => (pure ())

/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSUB_f_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let loop_r_lower := 0
      let loop_r_upper := (regs -i 1)
      let mut loop_vars := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPSub (← (Elem_read (← (D_read (n +i r))) e esize)) (← (Elem_read (← (D_read (m +i r))) e esize)) (← (StandardFPSCRValue ())))))))
          (pure loop_vars_1)
      (pure loop_vars))
  else
    (do
      match esize with
      | 16 => (S_set d ((Zeros (n := 16)) +++ (← (FPSub (Sail.BitVec.extractLsb (← (S_read n)) 15 0) (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ()))))))
      | 32 => (S_set d (← (FPSub (← (S_read n)) (← (S_read m)) (← (FPSCR_read ())))))
      | 64 => (D_set d (← (FPSub (← (D_read n)) (← (D_read m)) (← (FPSCR_read ())))))
      | _ => (pure ()))

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSUBHN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (pure ((← (Elem_read (← (Qin_read (Int.shiftr n 1))) e (2 *i esize))) - (← (Elem_read (← (Qin_read (Int.shiftr m 1))) e (2 *i esize)))))
        (D_set d (← (Elem_set (← (D_read d)) e esize (Sail.BitVec.extractLsb result ((2 *i esize) -i 1) esize))))
        (pure result)
    (pure loop_vars) ) : SailM (BitVec (2 * esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSUB_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize ((← (Elem_read (← (D_read (n +i r))) e esize)) - (← (Elem_read (← (D_read (m +i r))) e esize))))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_is_vsubw : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSUBL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (is_vsubw : Bool) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let op1 ← (( do (undefined_int ()) ) : SailM Int )
        let op1 ← (( do
          if (is_vsubw : Bool)
          then (do (asl_Int (← (Elem_read (← (Qin_read (Int.shiftr n 1))) e (2 *i esize))) is_unsigned))
          else (do (asl_Int (← (Elem_read (← (Din_read n)) e esize)) is_unsigned)) ) : SailM Int )
        let op1 := op1
        let result ← (pure (op1 -i (← (asl_Int (← (Elem_read (← (Din_read m)) e esize)) is_unsigned))))
        (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e (2 *i esize) (integer_subrange result ((2 *i esize) -i 1) 0))))
        (pure result)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VSWP_Op_A_txt (d : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((d == m) : Bool)
      then (D_set (d +i r) (← (__UNKNOWN_bits 64)))
      else
        (do
          (D_set (d +i r) (← (Din_read (m +i r))))
          (D_set (m +i r) (← (Din_read (d +i r)))))
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, k_is_vtbl : Bool, length : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem length [1, 2, 3, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VTBL_Op_A_txt (d__arg : Nat) (is_vtbl : Bool) (length : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let d : Int := d__arg
  let index ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let table3 ← (( do
    if ((length == 4) : Bool)
    then (D_read (n +i 3))
    else (pure (Zeros (n := 64))) ) : SailM (BitVec 64) )
  let table2 ← (( do
    if ((length ≥b 3) : Bool)
    then (D_read (n +i 2))
    else (pure (Zeros (n := 64))) ) : SailM (BitVec 64) )
  let table1 ← (( do
    if ((length ≥b 2) : Bool)
    then (D_read (n +i 1))
    else (pure (Zeros (n := 64))) ) : SailM (BitVec 64) )
  let table ← (( do (pure (((table3 +++ table2) +++ table1) +++ (← (D_read n)))) ) : SailM (BitVec 256) )
  let index ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 7
    let mut loop_vars := index
    for i in [loop_i_lower:loop_i_upper:1]i do
      let index := loop_vars
      loop_vars ← do
        let index ← (pure (BitVec.toNat (← (Elem_read (← (D_read m)) i 8))))
        let index := index
        if ((index <b (8 *i length)) : Bool)
        then (D_set d (← (Elem_set (← (D_read d)) i 8 (← (Elem_read table index 8)))))
        else
          (do
            if (is_vtbl : Bool)
            then (D_set d (← (Elem_set (← (D_read d)) i 8 (Zeros (n := 8)))))
            else (pure ()))
        (pure index)
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m__arg : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m__arg ∧ m__arg ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VTRN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m__arg : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let m : Int := m__arg
  (CheckAdvSIMDEnabled ())
  let h := (fdiv_int elements 2)
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((d == m) : Bool)
      then (D_set (d +i r) (← (__UNKNOWN_bits 64)))
      else
        (do
          let loop_e_lower := 0
          let loop_e_upper := (h -i 1)
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) ((2 *i e) +i 1) esize (← (Elem_read (← (Din_read (m +i r))) (2 *i e) esize)))))
              (D_set (m +i r) (← (Elem_set (← (D_read (m +i r))) (2 *i e) esize (← (Elem_read (← (Din_read (d +i r))) ((2 *i e) +i 1) esize)))))
          (pure loop_vars_1))
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VTST_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          if ((! (IsZero ((← (Elem_read (← (D_read (n +i r))) e esize)) &&& (← (Elem_read (← (D_read (m +i r))) e esize))))) : Bool)
          then (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (Ones (n := esize)))))
          else (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (Zeros (n := esize)))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d__arg : Nat, esize : Nat, m__arg : Nat, k_quadword_operation : Bool, 0 ≤ m__arg ∧ m__arg ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VUZP_Op_A_txt (d__arg : Nat) (esize : Nat) (m__arg : Nat) (quadword_operation : Bool) : SailM Unit := do
  let d : Int := d__arg
  let m : Int := m__arg
  let zipped_d ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let zipped_q ← (( do (undefined_bitvector 256) ) : SailM (BitVec 256) )
  (CheckAdvSIMDEnabled ())
  if (quadword_operation : Bool)
  then
    (do
      if ((d == m) : Bool)
      then (Q_set (Int.shiftr d 1) (← (__UNKNOWN_bits 128)))
      else
        (do
          let zipped_q ← (( do (pure ((← (Q_read (Int.shiftr m 1))) +++ (← (Q_read (Int.shiftr d 1))))) ) : SailM (BitVec 256) )
          let loop_e_lower := 0
          let loop_e_upper := ((Int.ediv 128 esize) -i 1)
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              (Q_set (Int.shiftr d 1) (← (Elem_set (← (Q_read (Int.shiftr d 1))) e esize (← (Elem_read zipped_q (2 *i e) esize)))))
              (Q_set (Int.shiftr m 1) (← (Elem_set (← (Q_read (Int.shiftr m 1))) e esize (← (Elem_read zipped_q ((2 *i e) +i 1) esize)))))
          (pure loop_vars_1)))
  else
    (do
      if ((d == m) : Bool)
      then (D_set d (← (__UNKNOWN_bits 64)))
      else
        (do
          let zipped_d ← (( do (pure ((← (D_read m)) +++ (← (D_read d)))) ) : SailM (BitVec 128) )
          let loop_e_lower := 0
          let loop_e_upper := ((Int.ediv 64 esize) -i 1)
          let mut loop_vars := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars
            loop_vars ← do
              (D_set d (← (Elem_set (← (D_read d)) e esize (← (Elem_read zipped_d (2 *i e) esize)))))
              (D_set m (← (Elem_set (← (D_read m)) e esize (← (Elem_read zipped_d ((2 *i e) +i 1) esize)))))
          (pure loop_vars)))

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, k_quadword_operation : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VZIP_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (quadword_operation : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  if (quadword_operation : Bool)
  then
    (do
      if ((d == m) : Bool)
      then (Q_set (Int.shiftr d 1) (← (__UNKNOWN_bits 128)))
      else
        (do
          let zipped_q ← (( do (undefined_bitvector 256) ) : SailM (BitVec 256) )
          let zipped_q ← (( do
            let loop_e_lower := 0
            let loop_e_upper := ((Int.ediv 128 esize) -i 1)
            let mut loop_vars_1 := zipped_q
            for e in [loop_e_lower:loop_e_upper:1]i do
              let zipped_q := loop_vars_1
              loop_vars_1 ← do
                let zipped_q ← (Elem_set zipped_q (2 *i e) esize (← (Elem_read (← (Q_read (Int.shiftr d 1))) e esize)))
                (Elem_set zipped_q ((2 *i e) +i 1) esize (← (Elem_read (← (Q_read (Int.shiftr m 1))) e esize)))
            (pure loop_vars_1) ) : SailM (BitVec 256) )
          (Q_set (Int.shiftr d 1) (Sail.BitVec.extractLsb zipped_q 127 0))
          (Q_set (Int.shiftr m 1) (Sail.BitVec.extractLsb zipped_q 255 128))))
  else
    (do
      if ((d == m) : Bool)
      then (D_set d (← (__UNKNOWN_bits 64)))
      else
        (do
          let zipped_d ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
          let zipped_d ← (( do
            let loop_e_lower := 0
            let loop_e_upper := ((Int.ediv 64 esize) -i 1)
            let mut loop_vars := zipped_d
            for e in [loop_e_lower:loop_e_upper:1]i do
              let zipped_d := loop_vars
              loop_vars ← do
                let zipped_d ← (Elem_set zipped_d (2 *i e) esize (← (Elem_read (← (D_read d)) e esize)))
                (Elem_set zipped_d ((2 *i e) +i 1) esize (← (Elem_read (← (D_read m)) e esize)))
            (pure loop_vars) ) : SailM (BitVec 128) )
          (D_set d (Sail.BitVec.extractLsb zipped_d 63 0))
          (D_set m (Sail.BitVec.extractLsb zipped_d 127 64))))

def execute_aarch32_instrs_WFE_Op_A_txt (_ : Unit) : SailM Unit := do
  if ((← (IsEventRegisterSet ())) : Bool)
  then (ClearEventRegister ())
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then (AArch32_CheckForWFxTrap EL1 WFxType_WFE)
      else (pure ())
      if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
           (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
           (EL2Enabled ())) <&&> (do
           (pure (! (← (IsInHost ()))))))) : Bool)
      then (AArch32_CheckForWFxTrap EL2 WFxType_WFE)
      else (pure ())
      if ((←((pure (HaveEL EL3)) <&&> (do
           (pure ((← readReg PSTATE).M != M32_Monitor))))) : Bool)
      then (AArch32_CheckForWFxTrap EL3 WFxType_WFE)
      else (pure ())
      let localtimeout := (Int.shiftl 1 64)
      (WaitForEvent localtimeout))

def execute_aarch32_instrs_WFI_Op_A_txt (_ : Unit) : SailM Unit := do
  if ((! (← (InterruptPending ()))) : Bool)
  then
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then (AArch32_CheckForWFxTrap EL1 WFxType_WFI)
      else (pure ())
      if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
           (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
           (EL2Enabled ())) <&&> (do
           (pure (! (← (IsInHost ()))))))) : Bool)
      then (AArch32_CheckForWFxTrap EL2 WFxType_WFI)
      else (pure ())
      if ((←((pure (HaveEL EL3)) <&&> (do
           (pure ((← readReg PSTATE).M != M32_Monitor))))) : Bool)
      then (AArch32_CheckForWFxTrap EL3 WFxType_WFI)
      else (pure ())
      let localtimeout := (Int.shiftl 1 64)
      (WaitForInterrupt localtimeout))
  else (pure ())

def execute_aarch32_instrs_YIELD_Op_A_txt (_ : Unit) : Unit :=
  (Hint_Yield ())

/-- Type quantifiers: k_affectA : Bool, k_affectF : Bool, k_affectI : Bool, k_changemode : Bool, k_disable : Bool, k_enable : Bool -/
def execute_aarch32_instrs_CPS_OpT_AS_txt (affectA : Bool) (affectF : Bool) (affectI : Bool) (changemode : Bool) (disable : Bool) (enable : Bool) (mode : (BitVec 5)) : SailM Unit := do
  if (((← readReg PSTATE).EL != EL0) : Bool)
  then
    (do
      if (enable : Bool)
      then
        (do
          if (affectA : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with A := 0#1 }
          else (pure ())
          if (affectI : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with I := 0#1 }
          else (pure ())
          if (affectF : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with F := 0#1 }
          else (pure ()))
      else (pure ())
      if (disable : Bool)
      then
        (do
          if (affectA : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with A := 1#1 }
          else (pure ())
          if (affectI : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with I := 1#1 }
          else (pure ())
          if (affectF : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with F := 1#1 }
          else (pure ()))
      else (pure ())
      if (changemode : Bool)
      then (AArch32_WriteModeByInstr mode)
      else (pure ()))
  else (pure ())

def execute_aarch32_instrs_ERET_Op_AS_txt (_ : Unit) : SailM Unit := do
  let new_pc_value ← (( do (undefined_bitvector 32) ) : SailM ELR_hyp_Type )
  if ((! (← (Halted ()))) : Bool)
  then
    (do
      if ((←((pure ((← readReg PSTATE).M == M32_User)) <||> (do
           (pure ((← readReg PSTATE).M == M32_System))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else
        (do
          let new_pc_value ← (( do
            if (((← readReg PSTATE).EL == EL2) : Bool)
            then (ELR_hyp_read ())
            else (R_read 14) ) : SailM ELR_hyp_Type )
          (AArch32_ExceptionReturn new_pc_value (← (SPSR_read (N := 32))))))
  else
    (do
      if (((← readReg PSTATE).M == M32_User) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if (((← readReg PSTATE).M == M32_System) : Bool)
          then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
          else
            (do
              let _ : Unit := (SynchronizeContext ())
              (DebugRestorePSR ()))))

def execute_aarch32_instrs_HVC_Op_AS_txt (imm16 : (BitVec 16)) : SailM Unit := do
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
       (pure ((← readReg PSTATE).EL == EL3))) <||> (do
       (pure (! (← (EL2Enabled ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let hvc_enable ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let hvc_enable ← (( do
    if ((HaveEL EL3) : Bool)
    then
      (do
        if ((←((ELUsingAArch32 EL3) <&&> (do
             (pure ((_get_SCR_Type_HCE (← readReg SCR)) == 0#1))) <&&> (do
             (pure ((← readReg PSTATE).EL == EL2))))) : Bool)
        then sailThrow ((Error_Unpredictable ()))
        else (do (pure (_get_SCRType_HCE (← (SCR_GEN_read ()))))))
    else
      (do
        if ((← (ELUsingAArch32 EL2)) : Bool)
        then (pure (Complement.complement (_get_HCR_Type_HCD (← (HCR_read ())))))
        else (pure (Complement.complement (_get_HCR_EL2_Type_HCD (← readReg HCR_EL2))))) ) : SailM (BitVec 1) )
  if ((hvc_enable == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (AArch32_CallHypervisor imm16)

/-- Type quantifiers: k_increment_name : Bool, n : Nat, k_wback : Bool, k_wordhigher : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDM_e_Op_AS_txt (increment_name : Bool) (n : Nat) (registers : (BitVec 15)) (wback : Bool) (wordhigher : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let length ← (( do (undefined_int ()) ) : SailM Int )
  let new_pc_value ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure ((← readReg PSTATE).M == M32_User)) <||> (do
           (pure ((← readReg PSTATE).M == M32_System))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else
        (do
          let length := ((4 *i (BitCount registers)) +i 4)
          let address ← (( do
            if (increment_name : Bool)
            then (R_read n)
            else (pure (BitVec.subInt (← (R_read n)) length)) ) : SailM (BitVec 32) )
          let address : (BitVec 32) :=
            if (wordhigher : Bool)
            then (BitVec.addInt address 4)
            else address
          let address ← (( do
            let loop_i_lower := 0
            let loop_i_upper := 14
            let mut loop_vars := address
            for i in [loop_i_lower:loop_i_upper:1]i do
              let address := loop_vars
              loop_vars ← do
                if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
                then
                  (do
                    (R_set i (← (MemS_read address 4)))
                    (pure (BitVec.addInt address 4)))
                else (pure address)
            (pure loop_vars) ) : SailM (BitVec 32) )
          let new_pc_value ← (( do (MemS_read address 4) ) : SailM (BitVec 32) )
          sail_assert ((0 ≤b n) && (n <b 15)) "src/instrs32.sail:40979.46-40979.47"
          if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 0#1)) : Bool)
          then
            (R_set n
              (← (do
                if (increment_name : Bool)
                then (pure (BitVec.addInt (← (R_read n)) length))
                else (pure (BitVec.subInt (← (R_read n)) length)))))
          else (pure ())
          if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
          then (R_set n (← (__UNKNOWN_bits 32)))
          else (pure ())
          (AArch32_ExceptionReturn new_pc_value (← (SPSR_read (N := 32))))))

/-- Type quantifiers: k_increment_name : Bool, n : Nat, k_wordhigher : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDM_u_Op_AS_txt (increment_name : Bool) (n : Nat) (registers : (BitVec 15)) (wordhigher : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let length ← (( do (undefined_int ()) ) : SailM Int )
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure ((← readReg PSTATE).M == M32_User)) <||> (do
           (pure ((← readReg PSTATE).M == M32_System))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else
        (do
          let length := (4 *i (BitCount registers))
          let address ← (( do
            if (increment_name : Bool)
            then (R_read n)
            else (pure (BitVec.subInt (← (R_read n)) length)) ) : SailM (BitVec 32) )
          let address : (BitVec 32) :=
            if (wordhigher : Bool)
            then (BitVec.addInt address 4)
            else address
          let address ← (( do
            let loop_i_lower := 0
            let loop_i_upper := 14
            let mut loop_vars := address
            for i in [loop_i_lower:loop_i_upper:1]i do
              let address := loop_vars
              loop_vars ← do
                if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
                then
                  (do
                    (Rmode_set i M32_User (← (MemS_read address 4)))
                    (pure (BitVec.addInt address 4)))
                else (pure address)
            (pure loop_vars) ) : SailM (BitVec 32) )
          (pure ())))

/-- Type quantifiers: d : Nat, k_read_spsr : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MRS_Op_AS_txt (d : Nat) (read_spsr : Bool) : SailM Unit := do
  let psr_val ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  if (read_spsr : Bool)
  then
    (do
      if ((←((pure ((← readReg PSTATE).M == M32_User)) <||> (do
           (pure ((← readReg PSTATE).M == M32_System))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (R_set d (← (SPSR_read (N := 32)))))
  else
    (do
      let mask : (BitVec 32) := 0b11111000111011110000001111011111#32
      let psr_val ← (( do (pure ((← (GetPSRFromPSTATE AArch32_NonDebugState 32)) &&& mask)) ) : SailM (BitVec 32) )
      let psr_val ← (( do
        if (((← readReg PSTATE).EL == EL0) : Bool)
        then
          (do
            let psr_val ← (pure (BitVec.update psr_val 22 (Bit (← (__UNKNOWN_bits 1)))))
            let psr_val ← (pure (Sail.BitVec.updateSubrange psr_val 9 6 (← (__UNKNOWN_bits 4))))
            (pure (Sail.BitVec.updateSubrange psr_val 4 0 (← (__UNKNOWN_bits 5)))))
        else (pure psr_val) ) : SailM (BitVec 32) )
      (R_set d psr_val))

/-- Type quantifiers: d : Nat, k_read_spsr : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MRS_br_Op_AS_txt (SYSm : (BitVec 5)) (d : Nat) (read_spsr : Bool) : SailM Unit := do
  let mode ← (( do (undefined_bitvector 5) ) : SailM (BitVec 5) )
  if (((← readReg PSTATE).EL == EL0) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else
    (do
      let mode ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
      if (read_spsr : Bool)
      then
        (do
          (SPSRaccessValid SYSm mode)
          match (SYSm : BitVec 5) with
          | 0b01110 => (R_set d (Sail.BitVec.extractLsb (← readReg SPSR_fiq) 31 0))
          | 0b10000 => (R_set d (Sail.BitVec.extractLsb (← readReg SPSR_irq) 31 0))
          | 0b10010 => (R_set d (Sail.BitVec.extractLsb (← (SPSR_svc_read ())) 31 0))
          | 0b10100 => (R_set d (Sail.BitVec.extractLsb (← readReg SPSR_abt) 31 0))
          | 0b10110 => (R_set d (Sail.BitVec.extractLsb (← readReg SPSR_und) 31 0))
          | 0b11100 =>
            (do
              if ((! (← (ELUsingAArch32 EL3))) : Bool)
              then (AArch64_MonitorModeTrap ())
              else (pure ())
              (R_set d (← readReg SPSR_mon)))
          | 0b11110 => (R_set d (Sail.BitVec.extractLsb (← (SPSR_hyp_read ())) 31 0))
          | _ => (pure ()))
      else
        (do
          let m ← (( do (undefined_int ()) ) : SailM Int )
          (BankedRegisterAccessValid SYSm mode)
          let b__0 := SYSm
          if (((Sail.BitVec.extractLsb b__0 4 3) == (0b00#2 : (BitVec 2))) : Bool)
          then
            (do
              let m := ((BitVec.toNat (Sail.BitVec.extractLsb SYSm 2 0)) +i 8)
              (R_set d (← (Rmode_read m M32_User))))
          else
            (do
              if (((Sail.BitVec.extractLsb b__0 4 3) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (do
                  let m := ((BitVec.toNat (Sail.BitVec.extractLsb SYSm 2 0)) +i 8)
                  (R_set d (← (Rmode_read m M32_FIQ))))
              else
                (do
                  if (((Sail.BitVec.extractLsb b__0 4 1) == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (do
                      let m := (14 -i (BitVec.toNat (BitVec.join1 [(BitVec.access SYSm 0)])))
                      (R_set d (← (Rmode_read m M32_IRQ))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb b__0 4 1) == (0x9#4 : (BitVec 4))) : Bool)
                      then
                        (do
                          let m := (14 -i (BitVec.toNat (BitVec.join1 [(BitVec.access SYSm 0)])))
                          (R_set d (← (Rmode_read m M32_Svc))))
                      else
                        (do
                          if (((Sail.BitVec.extractLsb b__0 4 1) == (0xA#4 : (BitVec 4))) : Bool)
                          then
                            (do
                              let m := (14 -i (BitVec.toNat (BitVec.join1 [(BitVec.access SYSm 0)])))
                              (R_set d (← (Rmode_read m M32_Abort))))
                          else
                            (do
                              if (((Sail.BitVec.extractLsb b__0 4 1) == (0xB#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  let m := (14 -i (BitVec.toNat (BitVec.join1 [(BitVec.access SYSm 0)])))
                                  (R_set d (← (Rmode_read m M32_Undef))))
                              else
                                (do
                                  if (((Sail.BitVec.extractLsb b__0 4 1) == (0xE#4 : (BitVec 4))) : Bool)
                                  then
                                    (do
                                      if ((! (← (ELUsingAArch32 EL3))) : Bool)
                                      then (AArch64_MonitorModeTrap ())
                                      else (pure ())
                                      let m := (14 -i (BitVec.toNat (BitVec.join1 [(BitVec.access SYSm 0)])))
                                      (R_set d (← (Rmode_read m M32_Monitor))))
                                  else
                                    (do
                                      if ((b__0 == (0b11110#5 : (BitVec 5))) : Bool)
                                      then (R_set d (← (ELR_hyp_read ())))
                                      else
                                        (do
                                          if ((b__0 == (0b11111#5 : (BitVec 5))) : Bool)
                                          then (R_set d (← (Rmode_read 13 M32_Hyp)))
                                          else (pure ())))))))))))

/-- Type quantifiers: n : Nat, k_write_spsr : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_MSR_br_Op_AS_txt (SYSm : (BitVec 5)) (n : Nat) (write_spsr : Bool) : SailM Unit := do
  let mode ← (( do (undefined_bitvector 5) ) : SailM (BitVec 5) )
  if (((← readReg PSTATE).EL == EL0) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else
    (do
      let mode ← (( do (pure (← readReg PSTATE).M) ) : SailM (BitVec 5) )
      if (write_spsr : Bool)
      then
        (do
          (SPSRaccessValid SYSm mode)
          match (SYSm : BitVec 5) with
          | 0b01110 => writeReg SPSR_fiq (Sail.BitVec.updateSubrange (← readReg SPSR_fiq) 31 0 (← (R_read n)))
          | 0b10000 => writeReg SPSR_irq (Sail.BitVec.updateSubrange (← readReg SPSR_irq) 31 0 (← (R_read n)))
          | 0b10010 => (SPSR_svc_write (Mk_SPSR_svc_Type (Sail.BitVec.updateSubrange (← (SPSR_svc_read ())) 31 0 (← (R_read n)))))
          | 0b10100 => writeReg SPSR_abt (Sail.BitVec.updateSubrange (← readReg SPSR_abt) 31 0 (← (R_read n)))
          | 0b10110 => writeReg SPSR_und (Sail.BitVec.updateSubrange (← readReg SPSR_und) 31 0 (← (R_read n)))
          | 0b11100 =>
            (do
              if ((! (← (ELUsingAArch32 EL3))) : Bool)
              then (AArch64_MonitorModeTrap ())
              else (pure ())
              writeReg SPSR_mon (Sail.BitVec.updateSubrange (← readReg SPSR_mon) 31 0 (← (R_read n))))
          | 0b11110 => (SPSR_hyp_write (Mk_SPSR_hyp_Type (Sail.BitVec.updateSubrange (← (SPSR_hyp_read ())) 31 0 (← (R_read n)))))
          | _ => (pure ()))
      else
        (do
          let m ← (( do (undefined_int ()) ) : SailM Int )
          (BankedRegisterAccessValid SYSm mode)
          let b__0 := SYSm
          if (((Sail.BitVec.extractLsb b__0 4 3) == (0b00#2 : (BitVec 2))) : Bool)
          then
            (do
              let m := ((BitVec.toNat (Sail.BitVec.extractLsb SYSm 2 0)) +i 8)
              (Rmode_set m M32_User (← (R_read n))))
          else
            (do
              if (((Sail.BitVec.extractLsb b__0 4 3) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (do
                  let m := ((BitVec.toNat (Sail.BitVec.extractLsb SYSm 2 0)) +i 8)
                  (Rmode_set m M32_FIQ (← (R_read n))))
              else
                (do
                  if (((Sail.BitVec.extractLsb b__0 4 1) == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (do
                      let m := (14 -i (BitVec.toNat (BitVec.join1 [(BitVec.access SYSm 0)])))
                      (Rmode_set m M32_IRQ (← (R_read n))))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb b__0 4 1) == (0x9#4 : (BitVec 4))) : Bool)
                      then
                        (do
                          let m := (14 -i (BitVec.toNat (BitVec.join1 [(BitVec.access SYSm 0)])))
                          (Rmode_set m M32_Svc (← (R_read n))))
                      else
                        (do
                          if (((Sail.BitVec.extractLsb b__0 4 1) == (0xA#4 : (BitVec 4))) : Bool)
                          then
                            (do
                              let m := (14 -i (BitVec.toNat (BitVec.join1 [(BitVec.access SYSm 0)])))
                              (Rmode_set m M32_Abort (← (R_read n))))
                          else
                            (do
                              if (((Sail.BitVec.extractLsb b__0 4 1) == (0xB#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  let m := (14 -i (BitVec.toNat (BitVec.join1 [(BitVec.access SYSm 0)])))
                                  (Rmode_set m M32_Undef (← (R_read n))))
                              else
                                (do
                                  if (((Sail.BitVec.extractLsb b__0 4 1) == (0xE#4 : (BitVec 4))) : Bool)
                                  then
                                    (do
                                      if ((! (← (ELUsingAArch32 EL3))) : Bool)
                                      then (AArch64_MonitorModeTrap ())
                                      else (pure ())
                                      let m := (14 -i (BitVec.toNat (BitVec.join1 [(BitVec.access SYSm 0)])))
                                      (Rmode_set m M32_Monitor (← (R_read n))))
                                  else
                                    (do
                                      if ((b__0 == (0b11110#5 : (BitVec 5))) : Bool)
                                      then (ELR_hyp_write (← (R_read n)))
                                      else
                                        (do
                                          if ((b__0 == (0b11111#5 : (BitVec 5))) : Bool)
                                          then (Rmode_set 13 M32_Hyp (← (R_read n)))
                                          else (pure ())))))))))))

/-- Type quantifiers: k_write_spsr : Bool -/
def execute_aarch32_instrs_MSR_i_Op_AS_txt (imm32 : (BitVec 32)) (mask : (BitVec 4)) (write_spsr : Bool) : SailM Unit := do
  if (write_spsr : Bool)
  then
    (do
      if ((←((pure ((← readReg PSTATE).M == M32_User)) <||> (do
           (pure ((← readReg PSTATE).M == M32_System))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (SPSRWriteByInstr imm32 mask))
  else (CPSRWriteByInstr imm32 mask)

/-- Type quantifiers: n : Nat, k_write_spsr : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_MSR_r_Op_AS_txt (mask : (BitVec 4)) (n : Nat) (write_spsr : Bool) : SailM Unit := do
  if (write_spsr : Bool)
  then
    (do
      if ((←((pure ((← readReg PSTATE).M == M32_User)) <||> (do
           (pure ((← readReg PSTATE).M == M32_System))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (SPSRWriteByInstr (← (R_read n)) mask))
  else (CPSRWriteByInstr (← (R_read n)) mask)

/-- Type quantifiers: k_increment_name : Bool, n : Nat, k_wback : Bool, k_wordhigher : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_RFE_Op_AS_txt (increment_name : Bool) (n : Nat) (wback : Bool) (wordhigher : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let new_pc_value ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let spsr ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else
        (do
          let address ← (( do
            if (increment_name : Bool)
            then (R_read n)
            else (pure (BitVec.subInt (← (R_read n)) 8)) ) : SailM (BitVec 32) )
          let address : (BitVec 32) :=
            if (wordhigher : Bool)
            then (BitVec.addInt address 4)
            else address
          let new_pc_value ← (( do (MemA_read address 4) ) : SailM (BitVec 32) )
          let spsr ← (( do (MemA_read (BitVec.addInt address 4) 4) ) : SailM (BitVec 32) )
          if (wback : Bool)
          then
            (R_set n
              (← (do
                if (increment_name : Bool)
                then (pure (BitVec.addInt (← (R_read n)) 8))
                else (pure (BitVec.subInt (← (R_read n)) 8)))))
          else (pure ())
          (AArch32_ExceptionReturn new_pc_value spsr)))

def execute_aarch32_instrs_SMC_Op_AS_txt (_ : Unit) : SailM Unit := do
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  (AArch32_CheckForSMCUndefOrTrap ())
  if ((! (← (ELUsingAArch32 EL3))) : Bool)
  then
    (do
      if (((_get_SCR_EL3_Type_SMD (← readReg SCR_EL3)) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ()))
  else
    (do
      if (((_get_SCR_Type_SCD (← readReg SCR)) == 1#1) : Bool)
      then
        (do
          if ((BEq.beq (← (CurrentSecurityState ())) SS_Secure) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_SMD) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_NOP) || (BEq.beq c Constraint_UNDEF)) "src/instrs32.sail:41695.66-41695.67"
              if ((BEq.beq c Constraint_NOP) : Bool)
              then (EndOfInstruction ())
              else (pure ()))
          else (pure ())
          (sailThrow ((Error_Undefined ())) : SailM Unit))
      else (pure ()))
  if ((! (← (ELUsingAArch32 EL3))) : Bool)
  then (AArch64_CallSecureMonitor (Zeros (n := 16)))
  else (AArch32_TakeSMCException ())

/-- Type quantifiers: k_increment_name : Bool, k_wback : Bool, k_wordhigher : Bool -/
def execute_aarch32_instrs_SRS_OpA_AS_txt (increment_name : Bool) (mode : (BitVec 5)) (wback : Bool) (wordhigher : Bool) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure ((← readReg PSTATE).M == M32_User)) <||> (do
       (pure ((← readReg PSTATE).M == M32_System))))) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else
    (do
      if ((mode == M32_Hyp) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else
        (do
          if ((mode == M32_Monitor) : Bool)
          then
            (do
              if ((←((pure (! (HaveEL EL3))) <||> (do
                   (pure (bne (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
              then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
              else
                (do
                  if ((! (← (ELUsingAArch32 EL3))) : Bool)
                  then (AArch64_MonitorModeTrap ())
                  else (pure ())))
          else
            (do
              if ((← (BadMode mode)) : Bool)
              then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
              else (pure ()))))
  let base ← (( do (Rmode_read 13 mode) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (increment_name : Bool)
    then base
    else (BitVec.subInt base 8)
  let address : (BitVec 32) :=
    if (wordhigher : Bool)
    then (BitVec.addInt address 4)
    else address
  (MemA_set address 4 (← (LR_read ())))
  (MemA_set (BitVec.addInt address 4) 4 (← (SPSR_read (N := (8 *i 4)))))
  if (wback : Bool)
  then
    (Rmode_set 13 mode
      (if (increment_name : Bool)
      then (BitVec.addInt base 8)
      else (BitVec.subInt base 8)))
  else (pure ())

/-- Type quantifiers: k_increment_name : Bool, k_wback : Bool, k_wordhigher : Bool -/
def execute_aarch32_instrs_SRS_OpT_AS_txt (increment_name : Bool) (mode : (BitVec 5)) (wback : Bool) (wordhigher : Bool) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure ((← readReg PSTATE).M == M32_User)) <||> (do
       (pure ((← readReg PSTATE).M == M32_System))))) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else
    (do
      if ((mode == M32_Hyp) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else
        (do
          if ((mode == M32_Monitor) : Bool)
          then
            (do
              if ((←((pure (! (HaveEL EL3))) <||> (do
                   (pure (bne (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
              then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
              else
                (do
                  if ((! (← (ELUsingAArch32 EL3))) : Bool)
                  then (AArch64_MonitorModeTrap ())
                  else (pure ())))
          else
            (do
              if ((← (BadMode mode)) : Bool)
              then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
              else (pure ()))))
  let base ← (( do (Rmode_read 13 mode) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (increment_name : Bool)
    then base
    else (BitVec.subInt base 8)
  let address : (BitVec 32) :=
    if (wordhigher : Bool)
    then (BitVec.addInt address 4)
    else address
  (MemA_set address 4 (← (LR_read ())))
  (MemA_set (BitVec.addInt address 4) 4 (← (SPSR_read (N := (8 *i 4)))))
  if (wback : Bool)
  then
    (Rmode_set 13 mode
      (if (increment_name : Bool)
      then (BitVec.addInt base 8)
      else (BitVec.subInt base 8)))
  else (pure ())

/-- Type quantifiers: k_increment_name : Bool, n : Nat, k_wordhigher : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STM_u_Op_AS_txt (increment_name : Bool) (n : Nat) (registers : (BitVec 16)) (wordhigher : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let length ← (( do (undefined_int ()) ) : SailM Int )
  if (((← readReg PSTATE).EL == EL2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure ((← readReg PSTATE).M == M32_User)) <||> (do
           (pure ((← readReg PSTATE).M == M32_System))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else
        (do
          let length := (4 *i (BitCount registers))
          let address ← (( do
            if (increment_name : Bool)
            then (R_read n)
            else (pure (BitVec.subInt (← (R_read n)) length)) ) : SailM (BitVec 32) )
          let address : (BitVec 32) :=
            if (wordhigher : Bool)
            then (BitVec.addInt address 4)
            else address
          let address ← (( do
            let loop_i_lower := 0
            let loop_i_upper := 14
            let mut loop_vars := address
            for i in [loop_i_lower:loop_i_upper:1]i do
              let address := loop_vars
              loop_vars ← do
                if (((BitVec.join1 [(BitVec.access registers i)]) == 1#1) : Bool)
                then
                  (do
                    (MemS_set address 4 (← (Rmode_read i M32_User)))
                    (pure (BitVec.addInt address 4)))
                else (pure address)
            (pure loop_vars) ) : SailM (BitVec 32) )
          if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
          then (MemS_set address 4 (← (PCStoreValue ())))
          else (pure ())))

/-- Type quantifiers: t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_VMRS_Op_AS_txt (reg : (BitVec 4)) (t : Nat) : SailM Unit := do
  if ((reg == 0b0001#4) : Bool)
  then
    (do
      (CheckVFPEnabled true)
      if ((t == 15) : Bool)
      then
        (do
          let split_vec ← do (pure ((_get_FPSR_Type_N (← readReg FPSR)) +++ ((_get_FPSR_Type_Z (← readReg FPSR)) +++ ((_get_FPSR_Type_C (← readReg FPSR)) +++ (_get_FPSR_Type_V (← readReg FPSR))))))
          writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
          writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
          writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
          writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
      else (R_set t (← (FPSCR_read__1 ()))))
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          (CheckVFPEnabled false)
          (AArch32_CheckAdvSIMDOrFPRegisterTraps reg)
          match (reg : BitVec 4) with
          | 0b0000 => (R_set t (← readReg FPSID))
          | 0b0101 => (R_set t (← (MVFR2_read ())))
          | 0b0110 => (R_set t (← (MVFR1_read ())))
          | 0b0111 => (R_set t (← (MVFR0_read ())))
          | 0b1000 => (R_set t (← (FPEXC_read ())))
          | _ => (Unreachable ())))

/-- Type quantifiers: t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_VMSR_Op_AS_txt (reg : (BitVec 4)) (t : Nat) : SailM Unit := do
  if ((reg == 0b0001#4) : Bool)
  then
    (do
      (CheckVFPEnabled true)
      (FPSCR_write (Mk_FPSCR_Type (← (R_read t)))))
  else
    (do
      if (((← readReg PSTATE).EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          (CheckVFPEnabled false)
          match (reg : BitVec 4) with
          | 0b0000 => (pure ())
          | 0b1000 => (FPEXC_write (Mk_FPEXC_Type (← (R_read t))))
          | _ => (Unreachable ())))

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_AESD_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let op1 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let op2 ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftr d 1) (← (AESInvSubBytes (AESInvShiftRows (op1 ^^^ op2)))))

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_AESE_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let op1 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let op2 ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftr d 1) (← (AESSubBytes (AESShiftRows (op1 ^^^ op2)))))

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_AESIMC_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  (Q_set (Int.shiftr d 1) (← (AESInvMixColumns (← (Q_read (Int.shiftr m 1))))))

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_AESMC_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  (Q_set (Int.shiftr d 1) (← (AESMixColumns (← (Q_read (Int.shiftr m 1))))))

/-- Type quantifiers: k_crc32c : Bool, d : Nat, m : Nat, n : Nat, size : Nat, List.elem size [8, 16, 32, 64] ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_CRC32_Op_A_txt (crc32c : Bool) (d : Nat) (m : Nat) (n : Nat) (size : Nat) : SailM Unit := do
  let acc ← (( do (R_read n) ) : SailM (BitVec 32) )
  sail_assert ((size -i 1) <b 32) "src/instrs32.sail:42465.37-42465.38"
  let val_name ← (( do (pure (Sail.BitVec.extractLsb (← (R_read m)) (size -i 1) 0)) ) : SailM (BitVec (0 + (size - 1 - 0 + 1))) )
  let poly : (BitVec 32) :=
    (integer_subrange
      (if (crc32c : Bool)
      then (BitVec.toNat 0x1EDC6F41#32)
      else (BitVec.toNat 0x04C11DB7#32)) 31 0)
  let tempacc ← (( do (pure ((← (BitReverse acc)) +++ (Zeros (n := size)))) ) : SailM (BitVec (32 + size)) )
  let tempval ← (( do (pure ((← (BitReverse val_name)) +++ (Zeros (n := 32)))) ) : SailM (BitVec (0 + (size - 1 - 0 + 1) + 32)) )
  (R_set d (← (BitReverse (← (Poly32Mod2 (tempacc ^^^ tempval) poly)))))

def execute_aarch32_instrs_DCPS1_Op_A_txt (_ : Unit) : SailM Unit := do
  let LR_svc ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let tge ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((EL2Enabled ()) <&&> (do
       (pure ((← readReg PSTATE).EL == EL0))))) : Bool)
  then
    (do
      let tge ← (( do
        if ((← (ELUsingAArch32 EL2)) : Bool)
        then (pure (_get_HCR_Type_TGE (← (HCR_read ()))))
        else (pure (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) ) : SailM (BitVec 1) )
      if ((tge == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ()))
  else (pure ())
  if ((←((pure ((← readReg PSTATE).EL != EL0)) <||> (do
       (ELUsingAArch32 EL1)))) : Bool)
  then
    (do
      if (((← readReg PSTATE).M == M32_Monitor) : Bool)
      then writeReg SCR (Sail.BitVec.updateSubrange (← readReg SCR) 0 0 0#1)
      else (pure ())
      if (((← readReg PSTATE).EL != EL2) : Bool)
      then
        (do
          (AArch32_WriteMode M32_Svc)
          writeReg PSTATE { (← readReg PSTATE) with E := ← (do (pure (_get_SCTLR_Type_EE (← (SCTLR_read__2 ()))))) }
          if ((←((HavePANExt ()) <&&> (do
               (pure ((_get_SCTLR_Type_SPAN (← (SCTLR_read__2 ()))) == 0#1))))) : Bool)
          then writeReg PSTATE { (← readReg PSTATE) with PAN := 1#1 }
          else (pure ())
          let LR_svc ← (__UNKNOWN_bits 32)
          (SPSR_svc_write (Mk_SPSR_svc_Type (← (__UNKNOWN_bits 32)))))
      else
        (do
          writeReg PSTATE { (← readReg PSTATE) with E := ← (do (pure (_get_HSCTLR_Type_EE (← (HSCTLR_read ()))))) }
          (ELR_hyp_write (← (__UNKNOWN_bits 32)))
          (HSR_write (Mk_HSR_Type (← (__UNKNOWN_bits 32))))
          (SPSR_hyp_write (Mk_SPSR_hyp_Type (← (__UNKNOWN_bits 32)))))
      (DLR_write (← (__UNKNOWN_bits 32)))
      (DSPSR_write (Mk_DSPSR_Type (← (__UNKNOWN_bits 32)))))
  else
    (do
      (AArch64_MaybeZeroRegisterUppers ())
      (MaybeZeroSVEUppers EL1)
      writeReg PSTATE { (← readReg PSTATE) with nRW := 0#1 }
      writeReg PSTATE { (← readReg PSTATE) with SP := 1#1 }
      writeReg PSTATE { (← readReg PSTATE) with EL := EL1 }
      if ((←((HavePANExt ()) <&&> (do
           (pure ((_get_SCTLR_EL1_Type_SPAN (← readReg SCTLR_EL1)) == 0#1))))) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with PAN := 1#1 }
      else (pure ())
      if ((← (HaveUAOExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with UAO := 0#1 }
      else (pure ())
      writeReg ELR_EL1 (← (__UNKNOWN_bits 64))
      writeReg ESR_EL1 (Mk_ESR_EL1_Type (← (__UNKNOWN_bits 64)))
      writeReg SPSR_EL1 (Mk_SPSR_EL1_Type (← (__UNKNOWN_bits 64)))
      writeReg DLR_EL0 (← (__UNKNOWN_bits 64))
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type (← (__UNKNOWN_bits 64)))
      if ((←((HaveIESB ()) <&&> (do
           (pure ((_get_SCTLR_EL1_Type_IESB (← readReg SCTLR_EL1)) == 1#1))) <&&> (do
           (pure (! (← (ConstrainUnpredictableBool Unpredictable_IESBinDebug))))))) : Bool)
      then (pure (SynchronizeErrors ()))
      else (pure ()))
  (UpdateEDSCRFields ())

def execute_aarch32_instrs_DCPS2_Op_A_txt (_ : Unit) : SailM Unit := do
  if ((←((pure (! (← (Halted ())))) <||> (do
       (pure (! (← (EL2Enabled ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((← (ELUsingAArch32 EL2)) : Bool)
  then
    (do
      (AArch32_WriteMode M32_Hyp)
      writeReg PSTATE { (← readReg PSTATE) with E := ← (do (pure (_get_HSCTLR_Type_EE (← (HSCTLR_read ()))))) }
      (ELR_hyp_write (← (__UNKNOWN_bits 32)))
      (HSR_write (Mk_HSR_Type (← (__UNKNOWN_bits 32))))
      (SPSR_hyp_write (Mk_SPSR_hyp_Type (← (__UNKNOWN_bits 32))))
      (DLR_write (← (__UNKNOWN_bits 32)))
      (DSPSR_write (Mk_DSPSR_Type (← (__UNKNOWN_bits 32)))))
  else
    (do
      (AArch64_MaybeZeroRegisterUppers ())
      (MaybeZeroSVEUppers EL2)
      writeReg PSTATE { (← readReg PSTATE) with nRW := 0#1 }
      writeReg PSTATE { (← readReg PSTATE) with SP := 1#1 }
      writeReg PSTATE { (← readReg PSTATE) with EL := EL2 }
      if ((←((HavePANExt ()) <&&> (do
           (pure ((_get_SCTLR_EL2_Type_SPAN (← readReg SCTLR_EL2)) == 0#1))) <&&> (do
           (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))) <&&> (do
           (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with PAN := 1#1 }
      else (pure ())
      if ((← (HaveUAOExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with UAO := 0#1 }
      else (pure ())
      writeReg ELR_EL2 (← (__UNKNOWN_bits 64))
      writeReg ESR_EL2 (Mk_ESR_EL2_Type (← (__UNKNOWN_bits 64)))
      writeReg SPSR_EL2 (Mk_SPSR_EL2_Type (← (__UNKNOWN_bits 64)))
      writeReg DLR_EL0 (← (__UNKNOWN_bits 64))
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type (← (__UNKNOWN_bits 64)))
      if ((←((HaveIESB ()) <&&> (do
           (pure ((_get_SCTLR_EL2_Type_IESB (← readReg SCTLR_EL2)) == 1#1))) <&&> (do
           (pure (! (← (ConstrainUnpredictableBool Unpredictable_IESBinDebug))))))) : Bool)
      then (pure (SynchronizeErrors ()))
      else (pure ()))
  (UpdateEDSCRFields ())

def execute_aarch32_instrs_DCPS3_Op_A_txt (_ : Unit) : SailM Unit := do
  let from_secure ← (( do (undefined_bool ()) ) : SailM Bool )
  let sync_errors ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((←((pure (! (← (Halted ())))) <||> (do
       (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((← (ELUsingAArch32 EL3)) : Bool)
  then
    (do
      let from_secure ← (( do (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure)) ) : SailM Bool )
      if (((← readReg PSTATE).M == M32_Monitor) : Bool)
      then writeReg SCR (Sail.BitVec.updateSubrange (← readReg SCR) 0 0 0#1)
      else (pure ())
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
      else (pure ())
      writeReg PSTATE { (← readReg PSTATE) with E := ← (do (pure (_get_SCTLR_Type_EE (← (SCTLR_read__2 ()))))) }
      writeReg LR_mon (← (__UNKNOWN_bits 32))
      writeReg SPSR_mon (Mk_SPSR_mon_Type (← (__UNKNOWN_bits 32)))
      (DLR_write (← (__UNKNOWN_bits 32)))
      (DSPSR_write (Mk_DSPSR_Type (← (__UNKNOWN_bits 32)))))
  else
    (do
      (AArch64_MaybeZeroRegisterUppers ())
      (MaybeZeroSVEUppers EL3)
      writeReg PSTATE { (← readReg PSTATE) with nRW := 0#1 }
      writeReg PSTATE { (← readReg PSTATE) with SP := 1#1 }
      writeReg PSTATE { (← readReg PSTATE) with EL := EL3 }
      if ((← (HaveUAOExt ())) : Bool)
      then writeReg PSTATE { (← readReg PSTATE) with UAO := 0#1 }
      else (pure ())
      writeReg ELR_EL3 (← (__UNKNOWN_bits 64))
      writeReg ESR_EL3 (Mk_ESR_EL3_Type (← (__UNKNOWN_bits 64)))
      writeReg SPSR_EL3 (Mk_SPSR_EL3_Type (← (__UNKNOWN_bits 64)))
      writeReg DLR_EL0 (← (__UNKNOWN_bits 64))
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type (← (__UNKNOWN_bits 64)))
      let sync_errors ← (( do (HaveIESB ()) <&&> (do (pure ((_get_SCTLR_EL3_Type_IESB (← readReg SCTLR_EL3)) == 1#1))) ) : SailM Bool )
      let sync_errors ← (( do
        if ((←((HaveDoubleFaultExt ()) <&&> (do
             (pure ((← (EffectiveEA ())) == 1#1))) <&&> (do
             (pure ((_get_SCR_EL3_Type_NMEA (← readReg SCR_EL3)) == 1#1))))) : Bool)
        then (pure true)
        else (pure sync_errors) ) : SailM Bool )
      let sync_errors ← (( do
        if ((! (← (ConstrainUnpredictableBool Unpredictable_IESBinDebug))) : Bool)
        then (pure false)
        else (pure sync_errors) ) : SailM Bool )
      let _ : Unit :=
        if (sync_errors : Bool)
        then (SynchronizeErrors ())
        else ()
      (pure ()))
  (UpdateEDSCRFields ())

def execute_aarch32_instrs_HLT_Op_A_txt (_ : Unit) : SailM Unit := do
  let is_async : Bool := false
  (Halt__1 DebugHalt_HaltInstruction is_async)

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDA_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 4 false t true)
  (R_set t (← (MemO_read address 4)))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAB_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 1 false t true)
  (R_set t (Sail.BitVec.zeroExtend (← (MemO_read address 1)) 32))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAEX_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 4)
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 4 false t true)
  (R_set t (← (MemO_read address 4)))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAEXB_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 1)
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 1 false t true)
  (R_set t (Sail.BitVec.zeroExtend (← (MemO_read address 1)) 32))

/-- Type quantifiers: n : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAEXD_Op_A_txt (n : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 8)
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 8 false t true)
  let value_name ← (( do (MemO_read address 8) ) : SailM (BitVec 64) )
  (R_set t
    (← (do
      if ((← (BigEndian AccessType_GPR)) : Bool)
      then (pure (Sail.BitVec.extractLsb value_name 63 32))
      else (pure (Sail.BitVec.extractLsb value_name 31 0)))))
  (R_set t2
    (← (do
      if ((← (BigEndian AccessType_GPR)) : Bool)
      then (pure (Sail.BitVec.extractLsb value_name 31 0))
      else (pure (Sail.BitVec.extractLsb value_name 63 32)))))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAEXH_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 2)
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 2 false t true)
  (R_set t (Sail.BitVec.zeroExtend (← (MemO_read address 2)) 32))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDAH_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 2 false t true)
  (R_set t (Sail.BitVec.zeroExtend (← (MemO_read address 2)) 32))

def execute_aarch32_instrs_SEVL_Op_A_txt (_ : Unit) : SailM Unit := do
  (SendEventLocal ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1C_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let t ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  (CheckCryptoEnabled32 ())
  let x ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let y ← (( do (pure (Sail.BitVec.extractLsb (← (Q_read (Int.shiftr n 1))) 31 0)) ) : SailM (BitVec 32) )
  let w ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let (t, x, y) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := 3
    let mut loop_vars := (t, x, y)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (t, x, y) := loop_vars
      loop_vars ← do
        let t : (BitVec 32) := (SHAchoose (Sail.BitVec.extractLsb x 63 32) (Sail.BitVec.extractLsb x 95 64) (Sail.BitVec.extractLsb x 127 96))
        let y ← (pure (((y + (← (ROL (Sail.BitVec.extractLsb x 31 0) 5))) + t) + (← (Elem_read w e 32))))
        let x ← (pure (Sail.BitVec.updateSubrange x 63 32 (← (ROL (Sail.BitVec.extractLsb x 63 32) 30))))
        let split_vec ← do (ROL (y +++ x) 32)
        let y : (BitVec 32) := (Sail.BitVec.extractLsb split_vec 159 128)
        let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
        (pure (t, x, y))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 128) × (BitVec 32)) )
  (Q_set (Int.shiftr d 1) x)

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1H_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  (Q_set (Int.shiftr d 1) (Sail.BitVec.zeroExtend (← (ROL (Sail.BitVec.extractLsb (← (Q_read (Int.shiftr m 1))) 31 0) 30)) 128))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1M_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let t ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  (CheckCryptoEnabled32 ())
  let x ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let y ← (( do (pure (Sail.BitVec.extractLsb (← (Q_read (Int.shiftr n 1))) 31 0)) ) : SailM (BitVec 32) )
  let w ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let (t, x, y) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := 3
    let mut loop_vars := (t, x, y)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (t, x, y) := loop_vars
      loop_vars ← do
        let t : (BitVec 32) := (SHAmajority (Sail.BitVec.extractLsb x 63 32) (Sail.BitVec.extractLsb x 95 64) (Sail.BitVec.extractLsb x 127 96))
        let y ← (pure (((y + (← (ROL (Sail.BitVec.extractLsb x 31 0) 5))) + t) + (← (Elem_read w e 32))))
        let x ← (pure (Sail.BitVec.updateSubrange x 63 32 (← (ROL (Sail.BitVec.extractLsb x 63 32) 30))))
        let split_vec ← do (ROL (y +++ x) 32)
        let y : (BitVec 32) := (Sail.BitVec.extractLsb split_vec 159 128)
        let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
        (pure (t, x, y))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 128) × (BitVec 32)) )
  (Q_set (Int.shiftr d 1) x)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1P_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let t ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  (CheckCryptoEnabled32 ())
  let x ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let y ← (( do (pure (Sail.BitVec.extractLsb (← (Q_read (Int.shiftr n 1))) 31 0)) ) : SailM (BitVec 32) )
  let w ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let (t, x, y) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := 3
    let mut loop_vars := (t, x, y)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (t, x, y) := loop_vars
      loop_vars ← do
        let t : (BitVec 32) := (SHAparity (Sail.BitVec.extractLsb x 63 32) (Sail.BitVec.extractLsb x 95 64) (Sail.BitVec.extractLsb x 127 96))
        let y ← (pure (((y + (← (ROL (Sail.BitVec.extractLsb x 31 0) 5))) + t) + (← (Elem_read w e 32))))
        let x ← (pure (Sail.BitVec.updateSubrange x 63 32 (← (ROL (Sail.BitVec.extractLsb x 63 32) 30))))
        let split_vec ← do (ROL (y +++ x) 32)
        let y : (BitVec 32) := (Sail.BitVec.extractLsb split_vec 159 128)
        let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
        (pure (t, x, y))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 128) × (BitVec 32)) )
  (Q_set (Int.shiftr d 1) x)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1SU0_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let op1 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let op2 ← (( do (Q_read (Int.shiftr n 1)) ) : SailM (BitVec 128) )
  let op3 ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let op2 : (BitVec 128) := ((Sail.BitVec.extractLsb op2 63 0) +++ (Sail.BitVec.extractLsb op1 127 64))
  (Q_set (Int.shiftr d 1) ((op1 ^^^ op2) ^^^ op3))

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1SU1_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let X ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let Y ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let T : (BitVec 128) := (X ^^^ (Y >>> 32))
  let W0 ← (( do (ROL (Sail.BitVec.extractLsb T 31 0) 1) ) : SailM (BitVec 32) )
  let W1 ← (( do (ROL (Sail.BitVec.extractLsb T 63 32) 1) ) : SailM (BitVec 32) )
  let W2 ← (( do (ROL (Sail.BitVec.extractLsb T 95 64) 1) ) : SailM (BitVec 32) )
  let W3 ← (( do (pure ((← (ROL (Sail.BitVec.extractLsb T 127 96) 1)) ^^^ (← (ROL (Sail.BitVec.extractLsb T 31 0) 2)))) ) : SailM (BitVec 32) )
  (Q_set (Int.shiftr d 1) (((W3 +++ W2) +++ W1) +++ W0))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA256H_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let X ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let Y ← (( do (Q_read (Int.shiftr n 1)) ) : SailM (BitVec 128) )
  let W ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let part1 : Bool := true
  (Q_set (Int.shiftr d 1) (← (SHA256hash X Y W part1)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA256H2_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let X ← (( do (Q_read (Int.shiftr n 1)) ) : SailM (BitVec 128) )
  let Y ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let W ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let part1 : Bool := false
  (Q_set (Int.shiftr d 1) (← (SHA256hash X Y W part1)))

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA256SU0_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let elt ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  (CheckCryptoEnabled32 ())
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let x ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let y ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let t : (BitVec 128) := ((Sail.BitVec.extractLsb y 31 0) +++ (Sail.BitVec.extractLsb x 127 32))
  let (elt, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := 3
    let mut loop_vars := (elt, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (elt, result) := loop_vars
      loop_vars ← do
        let elt ← (Elem_read t e 32)
        let elt : (BitVec 32) := (((ROR elt 7) ^^^ (ROR elt 18)) ^^^ (elt >>> 3))
        let result ← (Elem_set result e 32 (elt + (← (Elem_read x e 32))))
        (pure (elt, result))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 128)) )
  (Q_set (Int.shiftr d 1) result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA256SU1_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let elt ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let x ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let y ← (( do (Q_read (Int.shiftr n 1)) ) : SailM (BitVec 128) )
  let z ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let T0 : (BitVec 128) := ((Sail.BitVec.extractLsb z 31 0) +++ (Sail.BitVec.extractLsb y 127 32))
  let T1 : (BitVec 64) := (Sail.BitVec.extractLsb z 127 64)
  let (elt, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := 1
    let mut loop_vars := (elt, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (elt, result) := loop_vars
      loop_vars ← do
        let elt ← (Elem_read T1 e 32)
        let elt : (BitVec 32) := (((ROR elt 17) ^^^ (ROR elt 19)) ^^^ (elt >>> 10))
        let elt ← (pure ((elt + (← (Elem_read x e 32))) + (← (Elem_read T0 e 32))))
        let result ← (Elem_set result e 32 elt)
        (pure (elt, result))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 128)) )
  let T1 : (BitVec 64) := (Sail.BitVec.extractLsb result 63 0)
  let (elt, result) ← (( do
    let loop_e_lower := 2
    let loop_e_upper := 3
    let mut loop_vars_1 := (elt, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (elt, result) := loop_vars_1
      loop_vars_1 ← do
        let elt ← (Elem_read T1 (e -i 2) 32)
        let elt : (BitVec 32) := (((ROR elt 17) ^^^ (ROR elt 19)) ^^^ (elt >>> 10))
        let elt ← (pure ((elt + (← (Elem_read x e 32))) + (← (Elem_read T0 e 32))))
        let result ← (Elem_set result e 32 elt)
        (pure (elt, result))
    (pure loop_vars_1) ) : SailM ((BitVec 32) × (BitVec 128)) )
  (Q_set (Int.shiftr d 1) result)

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STL_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 4 false t true)
  (MemO_set address 4 (← (R_read t)))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STLB_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 1 false t true)
  (MemO_set address 1 (Sail.BitVec.extractLsb (← (R_read t)) 7 0))

/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STLEX_Op_A_txt (d : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  if ((← (AArch32_ExclusiveMonitorsPass address 4)) : Bool)
  then
    (do
      let _ : Unit := (AArch32_SetLSInstructionSyndrome 4 false t true)
      (MemO_set address 4 (← (R_read t)))
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else (R_set d (Sail.BitVec.zeroExtend 1#1 32))

/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STLEXB_Op_A_txt (d : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  if ((← (AArch32_ExclusiveMonitorsPass address 1)) : Bool)
  then
    (do
      let _ : Unit := (AArch32_SetLSInstructionSyndrome 1 false t true)
      (MemO_set address 1 (Sail.BitVec.extractLsb (← (R_read t)) 7 0))
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else (R_set d (Sail.BitVec.zeroExtend 1#1 32))

/-- Type quantifiers: d : Nat, n : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STLEXD_Op_A_txt (d : Nat) (n : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let value_name ← (( do
    if ((← (BigEndian AccessType_GPR)) : Bool)
    then (pure ((← (R_read t)) +++ (← (R_read t2))))
    else (pure ((← (R_read t2)) +++ (← (R_read t)))) ) : SailM (BitVec 64) )
  if ((← (AArch32_ExclusiveMonitorsPass address 8)) : Bool)
  then
    (do
      let _ : Unit := (AArch32_SetLSInstructionSyndrome 8 false t true)
      (MemO_set address 8 value_name)
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else (R_set d (Sail.BitVec.zeroExtend 1#1 32))

/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STLEXH_Op_A_txt (d : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  if ((← (AArch32_ExclusiveMonitorsPass address 2)) : Bool)
  then
    (do
      let _ : Unit := (AArch32_SetLSInstructionSyndrome 2 false t true)
      (MemO_set address 2 (Sail.BitVec.extractLsb (← (R_read t)) 15 0))
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else (R_set d (Sail.BitVec.zeroExtend 1#1 32))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STLH_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let _ : Unit := (AArch32_SetLSInstructionSyndrome 2 false t true)
  (MemO_set address 2 (Sail.BitVec.extractLsb (← (R_read t)) 15 0))

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCVTA_asimd_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let loop_r_lower := 0
  let loop_r_upper := (regs -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_e_lower := 0
      let loop_e_upper := (elements -i 1)
      let mut loop_vars_1 := ()
      for e in [loop_e_lower:loop_e_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPToFixed (← (Elem_read (← (D_read (m +i r))) e esize)) 0 is_unsigned (← (StandardFPSCRValue ())) rounding esize)))))
      (pure loop_vars_1)
  (pure loop_vars)

/-- Type quantifiers: d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVTA_vfp_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 => (S_set d (← (FPToFixed (Sail.BitVec.extractLsb (← (S_read m)) 15 0) 0 is_unsigned (← (FPSCR_read ())) rounding 32)))
  | 32 => (S_set d (← (FPToFixed (← (S_read m)) 0 is_unsigned (← (FPSCR_read ())) rounding 32)))
  | 64 => (S_set d (← (FPToFixed (← (D_read m)) 0 is_unsigned (← (FPSCR_read ())) rounding 32)))
  | _ => (pure ())

/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, k_maximum : Bool, n : Nat, regs : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMAXNM_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (maximum : Bool) (n : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let op2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let (op1, op2) ← (( do
        let loop_r_lower := 0
        let loop_r_upper := (regs -i 1)
        let mut loop_vars := (op1, op2)
        for r in [loop_r_lower:loop_r_upper:1]i do
          let (op1, op2) := loop_vars
          loop_vars ← do
            let (op1, op2) ← (( do
              let loop_e_lower := 0
              let loop_e_upper := (elements -i 1)
              let mut loop_vars_1 := (op1, op2)
              for e in [loop_e_lower:loop_e_upper:1]i do
                let (op1, op2) := loop_vars_1
                loop_vars_1 ← do
                  let op1 ← (Elem_read (← (D_read (n +i r))) e esize)
                  let op2 ← (Elem_read (← (D_read (m +i r))) e esize)
                  if (maximum : Bool)
                  then (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPMaxNum op1 op2 (← (StandardFPSCRValue ())))))))
                  else (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize (← (FPMinNum op1 op2 (← (StandardFPSCRValue ())))))))
                  (pure (op1, op2))
              (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
            (pure (op1, op2))
        (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
      (pure ()))
  else
    (do
      match esize with
      | 16 =>
        (do
          if (maximum : Bool)
          then (S_set d ((Zeros (n := 16)) +++ (← (FPMaxNum (Sail.BitVec.extractLsb (← (S_read n)) 15 0) (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ()))))))
          else (S_set d ((Zeros (n := 16)) +++ (← (FPMinNum (Sail.BitVec.extractLsb (← (S_read n)) 15 0) (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ())))))))
      | 32 =>
        (do
          if (maximum : Bool)
          then (S_set d (← (FPMaxNum (← (S_read n)) (← (S_read m)) (← (FPSCR_read ())))))
          else (S_set d (← (FPMinNum (← (S_read n)) (← (S_read m)) (← (FPSCR_read ()))))))
      | 64 =>
        (do
          if (maximum : Bool)
          then (D_set d (← (FPMaxNum (← (D_read n)) (← (D_read m)) (← (FPSCR_read ())))))
          else (D_set d (← (FPMinNum (← (D_read n)) (← (D_read m)) (← (FPSCR_read ()))))))
      | _ => (pure ()))

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_exact : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRINTA_asimd_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (exact : Bool) (m : Nat) (regs : Nat) (rounding : FPRounding) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, result) := loop_vars
      loop_vars ← do
        let (op1, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, result) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (m +i r))) e esize)
              let result ← (FPRoundInt op1 (← (StandardFPSCRValue ())) rounding exact)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              (pure (op1, result))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d : Nat, esize : Nat, k_exact : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VRINTA_vfp_Op_A_txt (d : Nat) (esize : Nat) (exact : Bool) (m : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 => (S_set d ((Zeros (n := 16)) +++ (← (FPRoundInt (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ())) rounding exact))))
  | 32 => (S_set d (← (FPRoundInt (← (S_read m)) (← (FPSCR_read ())) rounding exact)))
  | 64 => (D_set d (← (FPRoundInt (← (D_read m)) (← (FPSCR_read ())) rounding exact)))
  | _ => (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_exact : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRINTX_asimd_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (exact : Bool) (m : Nat) (regs : Nat) (rounding : FPRounding) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, result) := loop_vars
      loop_vars ← do
        let (op1, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, result) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (m +i r))) e esize)
              let result ← (FPRoundInt op1 (← (StandardFPSCRValue ())) rounding exact)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              (pure (op1, result))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d : Nat, esize : Nat, k_exact : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VRINTX_vfp_Op_A_txt (d : Nat) (esize : Nat) (exact : Bool) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  let rounding ← (( do (FPRoundingMode (← (FPSCR_read ()))) ) : SailM FPRounding )
  match esize with
  | 16 => (S_set d ((Zeros (n := 16)) +++ (← (FPRoundInt (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ())) rounding exact))))
  | 32 => (S_set d (← (FPRoundInt (← (S_read m)) (← (FPSCR_read ())) rounding exact)))
  | 64 => (D_set d (← (FPRoundInt (← (D_read m)) (← (FPSCR_read ())) rounding exact)))
  | _ => (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_exact : Bool, m : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRINTZ_asimd_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (exact : Bool) (m : Nat) (regs : Nat) (rounding : FPRounding) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (op1, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (op1, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (op1, result) := loop_vars
      loop_vars ← do
        let (op1, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (op1, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (op1, result) := loop_vars_1
            loop_vars_1 ← do
              let op1 ← (Elem_read (← (D_read (m +i r))) e esize)
              let result ← (FPRoundInt op1 (← (StandardFPSCRValue ())) rounding exact)
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) e esize result)))
              (pure (op1, result))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (op1, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d : Nat, esize : Nat, k_exact : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VRINTZ_vfp_Op_A_txt (d : Nat) (esize : Nat) (exact : Bool) (m : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 => (S_set d ((Zeros (n := 16)) +++ (← (FPRoundInt (Sail.BitVec.extractLsb (← (S_read m)) 15 0) (← (FPSCR_read ())) rounding exact))))
  | 32 => (S_set d (← (FPRoundInt (← (S_read m)) (← (FPSCR_read ())) rounding exact)))
  | 64 => (D_set d (← (FPRoundInt (← (D_read m)) (← (FPSCR_read ())) rounding exact)))
  | _ => (pure ())

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VSEL_Op_A_txt (cond : (BitVec 4)) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (S_set d
      ((Zeros (n := 16)) +++ (Sail.BitVec.extractLsb
          (← (do
            if ((← (ConditionHolds cond)) : Bool)
            then (S_read n)
            else (S_read m))) 15 0)))
  | 32 =>
    (S_set d
      (← (do
        if ((← (ConditionHolds cond)) : Bool)
        then (S_read n)
        else (S_read m))))
  | 64 =>
    (D_set d
      (← (do
        if ((← (ConditionHolds cond)) : Bool)
        then (D_read n)
        else (D_read m))))
  | _ => (pure ())

def execute_aarch32_instrs_SETPAN_Op_A_txt (value_name : (BitVec 1)) : SailM Unit := do
  if (((← readReg PSTATE).EL != EL0) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with PAN := value_name }
  else (pure ())

def execute_aarch32_instrs_ESB_Op_A_txt (_ : Unit) : SailM Unit := do
  let _ : Unit := (SynchronizeErrors ())
  (AArch32_ESBOperation ())
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
       (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
       (EL2Enabled ())))) : Bool)
  then (AArch32_vESBOperation ())
  else (pure ())
  (TakeUnmaskedSErrorInterrupts ())

def execute_aarch32_instrs_TSB_Op_A_txt (_ : Unit) : Unit :=
  (TraceSynchronizationBarrier ())

def execute_aarch32_instrs_CSDB_Op_A_txt (_ : Unit) : Unit :=
  (ConsumptionOfSpeculativeDataBarrier ())

def execute_aarch32_instrs_SSBB_Op_A_txt (_ : Unit) : Unit :=
  (SpeculativeStoreBypassBarrierToVA ())

def execute_aarch32_instrs_PSSBB_Op_A_txt (_ : Unit) : Unit :=
  (SpeculativeStoreBypassBarrierToPA ())

/-- Type quantifiers: d : Nat, esize : Nat, k_is_signed : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VDOT_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_signed : Bool) : SailM Unit := do
  let operand1 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  (CheckAdvSIMDEnabled ())
  let (operand1, operand2, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (operand1, operand2, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (operand1, operand2, result) := loop_vars
      loop_vars ← do
        let operand1 ← (D_read (n +i r))
        let operand2 ← (D_read (m +i r))
        let result ← (D_read (d +i r))
        let element1 ← (( do (undefined_int ()) ) : SailM Int )
        let element2 ← (( do (undefined_int ()) ) : SailM Int )
        let (element1, element2, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := 1
          let mut loop_vars_1 := (element1, element2, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (element1, element2, result) := loop_vars_1
            loop_vars_1 ← do
              let res : Int := 0
              let (element1, element2, res) ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := (element1, element2, res)
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let (element1, element2, res) := loop_vars_2
                  loop_vars_2 ← do
                    let (element1, element2) ← (( do
                      if (is_signed : Bool)
                      then
                        (do
                          let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                          let element2 ← (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                          (pure (element1, element2)))
                      else
                        (do
                          let element1 ← (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                          let element2 ← (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                          (pure (element1, element2))) ) : SailM (Int × Int) )
                    let res : Int := (res +i (element1 *i element2))
                    (pure (element1, element2, res))
                (pure loop_vars_2) ) : SailM (Int × Int × Int) )
              let res := res
              let result ← (Elem_set result e esize (BitVec.addInt (← (Elem_read result e esize)) res))
              (pure (element1, element2, result))
          (pure loop_vars_1) ) : SailM (Int × Int × (BitVec 64)) )
        (D_set (d +i r) result)
        (pure (operand1, operand2, result))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: d : Nat, esize : Nat, index : Nat, k_is_signed : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VDOT_s_Op_A_txt (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_signed : Bool) : SailM Unit := do
  let operand1 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (D_read m) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  (CheckAdvSIMDEnabled ())
  let (operand1, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (operand1, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (operand1, result) := loop_vars
      loop_vars ← do
        let operand1 ← (D_read (n +i r))
        let result ← (D_read (d +i r))
        let element1 ← (( do (undefined_int ()) ) : SailM Int )
        let element2 ← (( do (undefined_int ()) ) : SailM Int )
        let (element1, element2, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := 1
          let mut loop_vars_1 := (element1, element2, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (element1, element2, result) := loop_vars_1
            loop_vars_1 ← do
              let res : Int := 0
              let (element1, element2, res) ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := (element1, element2, res)
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let (element1, element2, res) := loop_vars_2
                  loop_vars_2 ← do
                    let (element1, element2) ← (( do
                      if (is_signed : Bool)
                      then
                        (do
                          let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                          let element2 ← (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i index) +i i) (Int.ediv esize 4)))))
                          (pure (element1, element2)))
                      else
                        (do
                          let element1 ← (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                          let element2 ← (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i index) +i i) (Int.ediv esize 4)))))
                          (pure (element1, element2))) ) : SailM (Int × Int) )
                    let res : Int := (res +i (element1 *i element2))
                    (pure (element1, element2, res))
                (pure loop_vars_2) ) : SailM (Int × Int × Int) )
              let res := res
              let result ← (Elem_set result e esize (BitVec.addInt (← (Elem_read result e esize)) res))
              (pure (element1, element2, result))
          (pure loop_vars_1) ) : SailM (Int × Int × (BitVec 64)) )
        (D_set (d +i r) result)
        (pure (operand1, result))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VJCVT_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  let fltval ← (( do (D_read m) ) : SailM (BitVec 64) )
  let intval ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let Z ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Z, intval) ← (( do
    let (tup__0, tup__1) ← do (FPToFixedJS fltval (← (FPSCR_read ())) false 32)
    let intval : (BitVec 32) := tup__0
    let Z : (BitVec 1) := tup__1
    (pure (Z, intval)) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (FPSCR_write (Mk_FPSCR_Type (Sail.BitVec.updateSubrange (← (FPSCR_read__1 ())) 31 28 ((0#1 +++ Z) +++ 0b00#2))))
  (S_set d intval)

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCMLA_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (rot : (BitVec 2)) : SailM Unit := do
  let d : Int := d__arg
  let operand1 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand3 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let result2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (operand1, operand2, operand3, result1, result2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (operand1, operand2, operand3, result1, result2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (operand1, operand2, operand3, result1, result2) := loop_vars
      loop_vars ← do
        let operand1 ← (D_read (n +i r))
        let operand2 ← (D_read (m +i r))
        let operand3 ← (D_read (d +i r))
        let (result1, result2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := ((fdiv_int elements 2) -i 1)
          let mut loop_vars_1 := (result1, result2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (result1, result2) := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let element4 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let (element1, element2, element3, element4) ← (( do
                match (rot : BitVec 2) with
                | 0b00 =>
                  (do
                    let element1 ← (Elem_read operand2 (e *i 2) esize)
                    let element2 ← (Elem_read operand1 (e *i 2) esize)
                    let element3 ← (Elem_read operand2 ((e *i 2) +i 1) esize)
                    let element4 ← (Elem_read operand1 (e *i 2) esize)
                    (pure (element1, element2, element3, element4)))
                | 0b01 =>
                  (do
                    let element1 ← (FPNeg (← (Elem_read operand2 ((e *i 2) +i 1) esize)))
                    let element2 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
                    let element3 ← (Elem_read operand2 (e *i 2) esize)
                    let element4 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
                    (pure (element1, element2, element3, element4)))
                | 0b10 =>
                  (do
                    let element1 ← (FPNeg (← (Elem_read operand2 (e *i 2) esize)))
                    let element2 ← (Elem_read operand1 (e *i 2) esize)
                    let element3 ← (FPNeg (← (Elem_read operand2 ((e *i 2) +i 1) esize)))
                    let element4 ← (Elem_read operand1 (e *i 2) esize)
                    (pure (element1, element2, element3, element4)))
                | _ =>
                  (do
                    let element1 ← (Elem_read operand2 ((e *i 2) +i 1) esize)
                    let element2 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
                    let element3 ← (FPNeg (← (Elem_read operand2 (e *i 2) esize)))
                    let element4 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
                    (pure (element1, element2, element3, element4))) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize)) )
              let element4 := element4
              let element3 := element3
              let element2 := element2
              let element1 := element1
              let result1 ← (FPMulAdd (← (Elem_read operand3 (e *i 2) esize)) element2 element1 (← (StandardFPSCRValue ())))
              let result2 ← (FPMulAdd (← (Elem_read operand3 ((e *i 2) +i 1) esize)) element4 element3 (← (StandardFPSCRValue ())))
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) (e *i 2) esize result1)))
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) ((e *i 2) +i 1) esize result2)))
              (pure (result1, result2))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (operand1, operand2, operand3, result1, result2))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 64) × (BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ List.elem esize [16, 32] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCMLA_idx_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (regs : Nat) (rot : (BitVec 2)) : SailM Unit := do
  let d : Int := d__arg
  let operand1 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand3 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let result2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (operand1, operand2, operand3, result1, result2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (operand1, operand2, operand3, result1, result2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (operand1, operand2, operand3, result1, result2) := loop_vars
      loop_vars ← do
        let operand1 ← (D_read (n +i r))
        let operand2 ← (Din_read m)
        let operand3 ← (D_read (d +i r))
        let (result1, result2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := ((fdiv_int elements 2) -i 1)
          let mut loop_vars_1 := (result1, result2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (result1, result2) := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let element4 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let (element1, element2, element3, element4) ← (( do
                match (rot : BitVec 2) with
                | 0b00 =>
                  (do
                    let element1 ← (Elem_read operand2 (index *i 2) esize)
                    let element2 ← (Elem_read operand1 (e *i 2) esize)
                    let element3 ← (Elem_read operand2 ((index *i 2) +i 1) esize)
                    let element4 ← (Elem_read operand1 (e *i 2) esize)
                    (pure (element1, element2, element3, element4)))
                | 0b01 =>
                  (do
                    let element1 ← (FPNeg (← (Elem_read operand2 ((index *i 2) +i 1) esize)))
                    let element2 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
                    let element3 ← (Elem_read operand2 (index *i 2) esize)
                    let element4 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
                    (pure (element1, element2, element3, element4)))
                | 0b10 =>
                  (do
                    let element1 ← (FPNeg (← (Elem_read operand2 (index *i 2) esize)))
                    let element2 ← (Elem_read operand1 (e *i 2) esize)
                    let element3 ← (FPNeg (← (Elem_read operand2 ((index *i 2) +i 1) esize)))
                    let element4 ← (Elem_read operand1 (e *i 2) esize)
                    (pure (element1, element2, element3, element4)))
                | _ =>
                  (do
                    let element1 ← (Elem_read operand2 ((index *i 2) +i 1) esize)
                    let element2 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
                    let element3 ← (FPNeg (← (Elem_read operand2 (index *i 2) esize)))
                    let element4 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
                    (pure (element1, element2, element3, element4))) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize)) )
              let element4 := element4
              let element3 := element3
              let element2 := element2
              let element1 := element1
              let result1 ← (FPMulAdd (← (Elem_read operand3 (e *i 2) esize)) element2 element1 (← (StandardFPSCRValue ())))
              let result2 ← (FPMulAdd (← (Elem_read operand3 ((e *i 2) +i 1) esize)) element4 element3 (← (StandardFPSCRValue ())))
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) (e *i 2) esize result1)))
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) ((e *i 2) +i 1) esize result2)))
              (pure (result1, result2))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (operand1, operand2, operand3, result1, result2))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 64) × (BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCADD_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (rot : (BitVec 1)) : SailM Unit := do
  let d : Int := d__arg
  let operand1 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let result2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (operand1, operand2, result1, result2) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (operand1, operand2, result1, result2)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (operand1, operand2, result1, result2) := loop_vars
      loop_vars ← do
        let operand1 ← (D_read (n +i r))
        let operand2 ← (D_read (m +i r))
        let (result1, result2) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := ((fdiv_int elements 2) -i 1)
          let mut loop_vars_1 := (result1, result2)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (result1, result2) := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
              let (element1, element3) ← (( do
                match (rot : BitVec 1) with
                | 0 =>
                  (do
                    let element1 ← (FPNeg (← (Elem_read operand2 ((e *i 2) +i 1) esize)))
                    let element3 ← (Elem_read operand2 (e *i 2) esize)
                    (pure (element1, element3)))
                | _ =>
                  (do
                    let element1 ← (Elem_read operand2 ((e *i 2) +i 1) esize)
                    let element3 ← (FPNeg (← (Elem_read operand2 (e *i 2) esize)))
                    (pure (element1, element3))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              let element3 := element3
              let element1 := element1
              let result1 ← (FPAdd (← (Elem_read operand1 (e *i 2) esize)) element1 (← (StandardFPSCRValue ())))
              let result2 ← (FPAdd (← (Elem_read operand1 ((e *i 2) +i 1) esize)) element3 (← (StandardFPSCRValue ())))
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) (e *i 2) esize result1)))
              (D_set (d +i r) (← (Elem_set (← (D_read (d +i r))) ((e *i 2) +i 1) esize result2)))
              (pure (result1, result2))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec esize)) )
        (pure (operand1, operand2, result1, result2))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec esize) × (BitVec esize)) )
  (pure ())

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, m : Nat, n : Nat, regs : Nat, k_sub_op : Bool, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VFMAL_Op_A_txt (Q : (BitVec 1)) (d : Nat) (datasize : Nat) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let element1 ← (( do (undefined_bitvector (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
  let element2 ← (( do (undefined_bitvector (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
  let (operand1, operand2) ← (( do
    if ((Q == 0#1) : Bool)
    then
      (do
        sail_assert ((0 ≤b (datasize -i 1)) && ((datasize -i 1) <b 32)) "src/instrs32.sail:46899.68-46899.69"
        let operand1 ← (pure (Sail.BitVec.extractLsb (← (S_read n)) (datasize -i 1) 0))
        let operand2 ← (pure (Sail.BitVec.extractLsb (← (S_read m)) (datasize -i 1) 0))
        (pure (operand1, operand2)))
    else
      (do
        let operand1 ← (pure (Sail.BitVec.extractLsb (← (D_read n)) (datasize -i 1) 0))
        let operand2 ← (pure (Sail.BitVec.extractLsb (← (D_read m)) (datasize -i 1) 0))
        (pure (operand1, operand2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
  let (element1, element2, operand3, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (element1, element2, operand3, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (element1, element2, operand3, result) := loop_vars
      loop_vars ← do
        let operand3 ← (D_read (d +i r))
        let (element1, element2, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := 1
          let mut loop_vars_1 := (element1, element2, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (element1, element2, result) := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (Elem_read operand1 ((2 *i r) +i e) (Int.ediv esize 2))
              let element2 ← (Elem_read operand2 ((2 *i r) +i e) (Int.ediv esize 2))
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec (esize / 2)) )
              let result ← (Elem_set result e esize (← (FPMulAddH (← (Elem_read operand3 e esize)) element1 element2 (← (StandardFPSCRValue ())))))
              (pure (element1, element2, result))
          (pure loop_vars_1) ) : SailM ((BitVec (esize / 2)) × (BitVec (esize / 2)) × (BitVec 64)) )
        (D_set (d +i r) result)
        (pure (element1, element2, operand3, result))
    (pure loop_vars) ) : SailM ((BitVec (esize / 2)) × (BitVec (esize / 2)) × (BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, regs : Nat, k_sub_op : Bool, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VFMAL_i_Op_A_txt (Q : (BitVec 1)) (d : Nat) (datasize : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (regs : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let element1 ← (( do (undefined_bitvector (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
  let (operand1, operand2) ← (( do
    if ((Q == 0#1) : Bool)
    then
      (do
        sail_assert ((0 ≤b (datasize -i 1)) && ((datasize -i 1) <b 32)) "src/instrs32.sail:47001.68-47001.69"
        let operand1 ← (pure (Sail.BitVec.extractLsb (← (S_read n)) (datasize -i 1) 0))
        let operand2 ← (pure (Sail.BitVec.extractLsb (← (S_read m)) (datasize -i 1) 0))
        (pure (operand1, operand2)))
    else
      (do
        let operand1 ← (pure (Sail.BitVec.extractLsb (← (D_read n)) (datasize -i 1) 0))
        let operand2 ← (pure (Sail.BitVec.extractLsb (← (D_read m)) (datasize -i 1) 0))
        (pure (operand1, operand2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
  let element2 ← (( do (Elem_read operand2 index (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
  let (element1, operand3, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (element1, operand3, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (element1, operand3, result) := loop_vars
      loop_vars ← do
        let operand3 ← (D_read (d +i r))
        let (element1, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := 1
          let mut loop_vars_1 := (element1, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (element1, result) := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (Elem_read operand1 ((2 *i r) +i e) (Int.ediv esize 2))
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec (esize / 2)) )
              let result ← (Elem_set result e esize (← (FPMulAddH (← (Elem_read operand3 e esize)) element1 element2 (← (StandardFPSCRValue ())))))
              (pure (element1, result))
          (pure loop_vars_1) ) : SailM ((BitVec (esize / 2)) × (BitVec 64)) )
        (D_set (d +i r) result)
        (pure (element1, operand3, result))
    (pure loop_vars) ) : SailM ((BitVec (esize / 2)) × (BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VDOT_bf16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let operand1 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  (CheckAdvSIMDEnabled ())
  let (operand1, operand2, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (operand1, operand2, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (operand1, operand2, result) := loop_vars
      loop_vars ← do
        let operand1 ← (Din_read (n +i r))
        let operand2 ← (Din_read (m +i r))
        let result ← (Din_read (d +i r))
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := 1
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (FPAdd_BF16 (← (BFMulH elt1_a elt2_a)) (← (BFMulH elt1_b elt2_b))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 (← (FPAdd_BF16 (← (Elem_read result e 32)) sum)))
          (pure loop_vars_1) ) : SailM (BitVec 64) )
        (D_set (d +i r) result)
        (pure (operand1, operand2, result))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem i [0, 1] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VDOT_bf16_i_Op_A_txt (d : Nat) (i : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let operand1 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  (CheckAdvSIMDEnabled ())
  let operand2 ← (( do (Din_read m) ) : SailM (BitVec 64) )
  let (operand1, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (operand1, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (operand1, result) := loop_vars
      loop_vars ← do
        let operand1 ← (Din_read (n +i r))
        let result ← (Din_read (d +i r))
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := 1
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i i) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i i) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (FPAdd_BF16 (← (BFMulH elt1_a elt2_a)) (← (BFMulH elt1_b elt2_b))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 (← (FPAdd_BF16 (← (Elem_read result e 32)) sum)))
          (pure loop_vars_1) ) : SailM (BitVec 64) )
        (D_set (d +i r) result)
        (pure (operand1, result))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VMMLA_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let op1 ← (( do (Q_read (Int.shiftr n 1)) ) : SailM (BitVec 128) )
  let op2 ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let acc ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftr d 1) (← (BFMatMulAdd acc op1 op2)))

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVT_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let operand ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let _ : Unit := (EncodingSpecificOperations ())
      (CheckAdvSIMDEnabled ())
      let operand ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
      let result ← (( do
        let loop_e_lower := 0
        let loop_e_upper := 3
        let mut loop_vars := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars
          loop_vars ← do
            let op ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (Elem_set result e 16 (← (FPConvertBF__1 op (← (StandardFPSCRValue ())))))
        (pure loop_vars) ) : SailM (BitVec 64) )
      (D_set d result))
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVTB_bf16_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  (S_set d (Sail.BitVec.updateSubrange (← (S_read d)) 15 0 (← (FPConvertBF__1 (← (S_read m)) (← (FPSCR_read ()))))))

/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVTT_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  (S_set d (Sail.BitVec.updateSubrange (← (S_read d)) 31 16 (← (FPConvertBF__1 (← (S_read m)) (← (FPSCR_read ()))))))

/-- Type quantifiers: d : Nat, elements : Nat, m : Nat, n : Nat, sel : Nat, List.elem sel [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ elements = 4 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VFMA_bf_Op_A_txt (d : Nat) (elements : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (Q_read (Int.shiftr n 1)) ) : SailM (BitVec 128) )
  let operand2 ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let operand3 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (pure ((← (Elem_read operand1 ((2 *i e) +i sel) 16)) +++ (Zeros (n := 16)))) ) : SailM (BitVec 32) )
        let element2 ← (( do (pure ((← (Elem_read operand2 ((2 *i e) +i sel) 16)) +++ (Zeros (n := 16)))) ) : SailM (BitVec 32) )
        let addend ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        (Elem_set result e 32 (← (FPMulAdd addend element1 element2 (← (StandardFPSCRValue ())))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftr d 1) result)

/-- Type quantifiers: d : Nat, elements : Nat, i : Nat, m : Nat, n : Nat, sel : Nat, List.elem sel [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem i [0, 1, 2, 3] ∧ elements = 4 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VFMA_bfs_Op_A_txt (d : Nat) (elements : Nat) (i : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (Q_read (Int.shiftr n 1)) ) : SailM (BitVec 128) )
  let operand2 ← (( do (D_read m) ) : SailM (BitVec 64) )
  let operand3 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let element2 ← (( do (pure ((← (Elem_read operand2 i 16)) +++ (Zeros (n := 16)))) ) : SailM (BitVec 32) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (pure ((← (Elem_read operand1 ((2 *i e) +i sel) 16)) +++ (Zeros (n := 16)))) ) : SailM (BitVec 32) )
        let addend ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        (Elem_set result e 32 (← (FPMulAdd addend element1 element2 (← (StandardFPSCRValue ())))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftr d 1) result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_MMLA_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (Q_read (Int.shiftr n 1)) ) : SailM (BitVec 128) )
  let operand2 ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
  let addend ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftr d 1) (← (MatMulAdd addend operand1 operand2 op1_unsigned op2_unsigned)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VUSDOT_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let (element1, element2, operand1, operand2, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (element1, element2, operand1, operand2, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (element1, element2, operand1, operand2, result) := loop_vars
      loop_vars ← do
        let operand1 ← (Din_read (n +i r))
        let operand2 ← (Din_read (m +i r))
        let result ← (Din_read (d +i r))
        let (element1, element2, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := 1
          let mut loop_vars_1 := (element1, element2, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (element1, element2, result) := loop_vars_1
            loop_vars_1 ← do
              let res ← (( do (Elem_read result e 32) ) : SailM (BitVec 32) )
              let (element1, element2, res) ← (( do
                let loop_b_lower := 0
                let loop_b_upper := 3
                let mut loop_vars_2 := (element1, element2, res)
                for b in [loop_b_lower:loop_b_upper:1]i do
                  let (element1, element2, res) := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i b) 8))))
                    let element2 ← (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i b) 8))))
                    let res : (BitVec 32) := (BitVec.addInt res (element1 *i element2))
                    (pure (element1, element2, res))
                (pure loop_vars_2) ) : SailM (Int × Int × (BitVec 32)) )
              let result ← (Elem_set result e 32 res)
              (pure (element1, element2, result))
          (pure loop_vars_1) ) : SailM (Int × Int × (BitVec 64)) )
        (D_set (d +i r) result)
        (pure (element1, element2, operand1, operand2, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec 64) × (BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem i [0, 1] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_DOT_Op_A_txt (d : Nat) (i : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (regs : Nat) : SailM Unit := do
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (Din_read m) ) : SailM (BitVec 64) )
  let (element1, element2, operand1, result) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (regs -i 1)
    let mut loop_vars := (element1, element2, operand1, result)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (element1, element2, operand1, result) := loop_vars
      loop_vars ← do
        let operand1 ← (Din_read (n +i r))
        let result ← (Din_read (d +i r))
        let (element1, element2, result) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := 1
          let mut loop_vars_1 := (element1, element2, result)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (element1, element2, result) := loop_vars_1
            loop_vars_1 ← do
              let res ← (( do (Elem_read result e 32) ) : SailM (BitVec 32) )
              let (element1, element2, res) ← (( do
                let loop_b_lower := 0
                let loop_b_upper := 3
                let mut loop_vars_2 := (element1, element2, res)
                for b in [loop_b_lower:loop_b_upper:1]i do
                  let (element1, element2, res) := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (asl_Int (← (Elem_read operand1 ((4 *i e) +i b) 8)) op1_unsigned)
                    let element2 ← (asl_Int (← (Elem_read operand2 ((4 *i i) +i b) 8)) op2_unsigned)
                    let res : (BitVec 32) := (BitVec.addInt res (element1 *i element2))
                    (pure (element1, element2, res))
                (pure loop_vars_2) ) : SailM (Int × Int × (BitVec 32)) )
              let result ← (Elem_set result e 32 res)
              (pure (element1, element2, result))
          (pure loop_vars_1) ) : SailM (Int × Int × (BitVec 64)) )
        (D_set (d +i r) result)
        (pure (element1, element2, operand1, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec 64) × (BitVec 64)) )
  (pure ())

def execute_aarch32_instrs_CLRBHB_Op_A_txt (_ : Unit) : Unit :=
  (Hint_CLRBHB ())

def decode_aarch32_instrs_ADC_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:68.29-68.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_ADC_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_ADC_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADC_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_ADC_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:143.29-143.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_ADC_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADC_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_ADC_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADC_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_ADC_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADC_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:252.29-252.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADC_rr_Op_A_txt d m n s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_ADD_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:306.29-306.30"
      if (((Rn == 0b1111#4) && (S == 0#1)) : Bool)
      then (sailThrow ((Error_See "ADR")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "ADD (SP plus immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_ADD_i_OpA_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_ADD_i_T1enc_A_txt (imm3 : (BitVec 3)) (Rn : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm3 32)
      (execute_aarch32_instrs_ADD_i_OpT_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_ADD_i_T2enc_A_txt (Rdn : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_ADD_i_OpT_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_ADD_i_T3enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "CMN (immediate)")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "ADD (SP plus immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if ((((d == 15) && (! setflags)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADD_i_OpT_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_ADD_i_T4enc_A_txt (i : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "ADR")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "ADD (SP plus immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADD_i_OpT_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_ADD_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:481.29-481.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "ADD (SP plus register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_ADD_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADD_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_ADD_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADD_r_T2enc_A_txt (DN : (BitVec 1)) (Rm : (BitVec 4)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((((DN +++ Rdn) == 0b1101#4) || (Rm == 0b1101#4)) : Bool)
      then (sailThrow ((Error_See "ADD (SP plus register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (DN +++ Rdn))
      let n := d
      let m := (BitVec.toNat Rm)
      let setflags : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if (((n == 15) && (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure (d == 15)) <&&> (do
           (InITBlock ())) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADD_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADD_r_T3enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "CMN (register)")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "ADD (SP plus register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((((d == 15) && (! setflags)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADD_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADD_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:632.29-632.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADD_rr_Op_A_txt d m n s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_ADD_SP_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:685.29-685.30"
      let d := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_ADD_SP_i_Op_A_txt d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_ADD_SP_i_T1enc_A_txt (Rd : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      (execute_aarch32_instrs_ADD_SP_i_Op_A_txt d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_ADD_SP_i_T2enc_A_txt (imm7 : (BitVec 7)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := 13
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm7 +++ 0b00#2) 32)
      (execute_aarch32_instrs_ADD_SP_i_Op_A_txt d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_ADD_SP_i_T3enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "CMN (immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if (((d == 15) && (! setflags)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADD_SP_i_Op_A_txt d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_ADD_SP_i_T4enc_A_txt (i : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADD_SP_i_Op_A_txt d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_ADD_SP_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:820.29-820.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_ADD_SP_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADD_SP_r_T1enc_A_txt (DM : (BitVec 1)) (Rdm : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat (DM +++ Rdm))
      let m := (BitVec.toNat (DM +++ Rdm))
      let setflags : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if ((←((pure (d == 15)) <&&> (do
           (InITBlock ())) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_ADD_SP_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADD_SP_r_T2enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rm == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "encoding T1")) : SailM Unit)
      else (pure ())
      let d := 13
      let m := (BitVec.toNat Rm)
      let setflags : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_ADD_SP_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADD_SP_r_T3enc_A_txt (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "CMN (register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((((d == 15) && (! setflags)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADD_SP_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ADR_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:951.29-951.30"
      let d := (BitVec.toNat Rd)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      let add : Bool := true
      (execute_aarch32_instrs_ADR_Op_A_txt add d imm32))
  else (pure ())

def decode_aarch32_instrs_ADR_A2enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:972.29-972.30"
      let d := (BitVec.toNat Rd)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      let add : Bool := false
      (execute_aarch32_instrs_ADR_Op_A_txt add d imm32))
  else (pure ())

def decode_aarch32_instrs_ADR_T1enc_A_txt (Rd : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let add : Bool := true
      (execute_aarch32_instrs_ADR_Op_A_txt add d imm32))
  else (pure ())

def decode_aarch32_instrs_ADR_T2enc_A_txt (i : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      let add : Bool := false
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADR_Op_A_txt add d imm32))
  else (pure ())

def decode_aarch32_instrs_ADR_T3enc_A_txt (i : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      let add : Bool := true
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ADR_Op_A_txt add d imm32))
  else (pure ())

def decode_aarch32_instrs_AND_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1083.29-1083.30"
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (A32ExpandImm_C imm12 (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      (execute_aarch32_instrs_AND_i_Op_A_txt carry d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_AND_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "TST (immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (T32ExpandImm_C ((i +++ imm3) +++ imm8) (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      if ((((d == 15) && (! setflags)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_AND_i_Op_A_txt carry d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_AND_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1167.29-1167.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_AND_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_AND_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_AND_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_AND_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "TST (register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((((d == 15) && (! setflags)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_AND_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_AND_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1279.29-1279.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_AND_rr_Op_A_txt d m n s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_ASR_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let shift_n ← (( do
        let (_, __tup_1) ← do (DecodeImmShift 0b10#2 imm5)
        (pure __tup_1) ) : SailM Int )
      let shift_n := shift_n
      (execute_aarch32_instrs_ASR_i_Op_A_txt d m setflags shift_n))
  else (pure ())

def decode_aarch32_instrs_ASR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      (execute_aarch32_instrs_ASR_r_Op_A_txt d m n setflags))
  else (pure ())

def decode_aarch32_instrs_B_A1enc_A_txt (cond : (BitVec 4)) (imm24 : (BitVec 24)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1401.29-1401.30"
      let imm32 : (BitVec 32) := (sign_extend (imm24 +++ 0b00#2) 32)
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure ())

def decode_aarch32_instrs_B_T1enc_A_txt (cond : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1419.29-1419.30"
      if ((cond == 0b1110#4) : Bool)
      then (sailThrow ((Error_See "UDF")) : SailM Unit)
      else (pure ())
      if ((cond == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SVC")) : SailM Unit)
      else (pure ())
      let imm32 : (BitVec 32) := (sign_extend (imm8 +++ 0#1) 32)
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure ())

def decode_aarch32_instrs_B_T2enc_A_txt (imm11 : (BitVec 11)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (sign_extend (imm11 +++ 0#1) 32)
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure ())

def decode_aarch32_instrs_B_T3enc_A_txt (S : (BitVec 1)) (cond : (BitVec 4)) (imm6 : (BitVec 6)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm11 : (BitVec 11)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1465.29-1465.30"
      if (((Sail.BitVec.extractLsb cond 3 1) == 0b111#3) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      let imm32 : (BitVec 32) := (sign_extend (((((S +++ J2) +++ J1) +++ imm6) +++ imm11) +++ 0#1) 32)
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure ())

def decode_aarch32_instrs_B_T4enc_A_txt (S : (BitVec 1)) (imm10 : (BitVec 10)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm11 : (BitVec 11)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let I1 : (BitVec 1) := (Complement.complement (J1 ^^^ S))
      let I2 : (BitVec 1) := (Complement.complement (J2 ^^^ S))
      let imm32 : (BitVec 32) := (sign_extend (((((S +++ I1) +++ I2) +++ imm10) +++ imm11) +++ 0#1) 32)
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure ())

def decode_aarch32_instrs_BFC_A1enc_A_txt (cond : (BitVec 4)) (msb : (BitVec 5)) (Rd : (BitVec 4)) (lsb : (BitVec 5)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1527.29-1527.30"
      let d := (BitVec.toNat Rd)
      let msbit := (BitVec.toNat msb)
      let lsbit := (BitVec.toNat lsb)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((msbit <b lsbit) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BFC_Op_A_txt d lsbit msbit))
  else (pure ())

def decode_aarch32_instrs_BFC_T1enc_A_txt (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (msb : (BitVec 5)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let msbit := (BitVec.toNat msb)
      let lsbit := (BitVec.toNat (imm3 +++ imm2))
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((msbit <b lsbit) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BFC_Op_A_txt d lsbit msbit))
  else (pure ())

def decode_aarch32_instrs_BFI_A1enc_A_txt (cond : (BitVec 4)) (msb : (BitVec 5)) (Rd : (BitVec 4)) (lsb : (BitVec 5)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1595.29-1595.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "BFC")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let msbit := (BitVec.toNat msb)
      let lsbit := (BitVec.toNat lsb)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((msbit <b lsbit) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BFI_Op_A_txt d lsbit msbit n))
  else (pure ())

def decode_aarch32_instrs_BFI_T1enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (msb : (BitVec 5)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "BFC")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let msbit := (BitVec.toNat msb)
      let lsbit := (BitVec.toNat (imm3 +++ imm2))
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((msbit <b lsbit) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BFI_Op_A_txt d lsbit msbit n))
  else (pure ())

def decode_aarch32_instrs_BIC_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1687.29-1687.30"
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (A32ExpandImm_C imm12 (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      (execute_aarch32_instrs_BIC_i_Op_A_txt carry d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_BIC_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (T32ExpandImm_C ((i +++ imm3) +++ imm8) (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let carry := carry
      (execute_aarch32_instrs_BIC_i_Op_A_txt carry d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_BIC_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1770.29-1770.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_BIC_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_BIC_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_BIC_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_BIC_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_BIC_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_BIC_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1881.29-1881.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BIC_rr_Op_A_txt d m n s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_BKPT_A1enc_A_txt (cond : (BitVec 4)) (imm12 : (BitVec 12)) (imm4 : (BitVec 4)) : SailM Unit := do
  sail_assert (cond != 0b1111#4) "src/instrs32.sail:1917.25-1917.26"
  let imm16 : (BitVec 16) := (imm12 +++ imm4)
  if ((cond != 0b1110#4) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_BKPT_Op_A_txt imm16)

def decode_aarch32_instrs_BKPT_T1enc_A_txt (imm8 : (BitVec 8)) : SailM Unit := do
  let imm16 : (BitVec 16) := (Sail.BitVec.zeroExtend imm8 16)
  (execute_aarch32_instrs_BKPT_Op_A_txt imm16)

def decode_aarch32_instrs_BL_i_A1enc_A_txt (cond : (BitVec 4)) (imm24 : (BitVec 24)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:1968.29-1968.30"
      let imm32 : (BitVec 32) := (sign_extend (imm24 +++ 0b00#2) 32)
      let targetInstrSet : InstrSet := InstrSet_A32
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure ())

def decode_aarch32_instrs_BL_i_A2enc_A_txt (H : (BitVec 1)) (imm24 : (BitVec 24)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (sign_extend ((imm24 +++ H) +++ 0#1) 32)
      let targetInstrSet : InstrSet := InstrSet_T32
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure ())

def decode_aarch32_instrs_BL_i_T1enc_A_txt (S : (BitVec 1)) (imm10 : (BitVec 10)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm11 : (BitVec 11)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let I1 : (BitVec 1) := (Complement.complement (J1 ^^^ S))
      let I2 : (BitVec 1) := (Complement.complement (J2 ^^^ S))
      let imm32 : (BitVec 32) := (sign_extend (((((S +++ I1) +++ I2) +++ imm10) +++ imm11) +++ 0#1) 32)
      let targetInstrSet : InstrSet := InstrSet_T32
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure ())

def decode_aarch32_instrs_BL_i_T2enc_A_txt (S : (BitVec 1)) (imm10H : (BitVec 10)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm10L : (BitVec 10)) (H : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((H == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let I1 : (BitVec 1) := (Complement.complement (J1 ^^^ S))
      let I2 : (BitVec 1) := (Complement.complement (J2 ^^^ S))
      let imm32 : (BitVec 32) := (sign_extend (((((S +++ I1) +++ I2) +++ imm10H) +++ imm10L) +++ 0b00#2) 32)
      let targetInstrSet : InstrSet := InstrSet_A32
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure ())

def decode_aarch32_instrs_BLX_r_A1enc_A_txt (cond : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2077.29-2077.30"
      let m := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BLX_r_Op_A_txt m))
  else (pure ())

def decode_aarch32_instrs_BLX_r_T1enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BLX_r_Op_A_txt m))
  else (pure ())

def decode_aarch32_instrs_BX_A1enc_A_txt (cond : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2135.29-2135.30"
      let m := (BitVec.toNat Rm)
      (execute_aarch32_instrs_BX_Op_A_txt m))
  else (pure ())

def decode_aarch32_instrs_BX_T1enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m := (BitVec.toNat Rm)
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BX_Op_A_txt m))
  else (pure ())

def decode_aarch32_instrs_BXJ_A1enc_A_txt (cond : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2187.29-2187.30"
      let m := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BXJ_Op_A_txt m))
  else (pure ())

def decode_aarch32_instrs_BXJ_T1enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_BXJ_Op_A_txt m))
  else (pure ())

def decode_aarch32_instrs_CBNZ_T1enc_A_txt (op : (BitVec 1)) (i : (BitVec 1)) (imm5 : (BitVec 5)) (Rn : (BitVec 3)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm5) +++ 0#1) 32)
  let nonzero : Bool := (op == 1#1)
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_CBNZ_Op_A_txt imm32 n nonzero)

def decode_aarch32_instrs_CLREX_A1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_CLREX_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_CLREX_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_CLREX_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_CLZ_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2321.29-2321.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_CLZ_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_CLZ_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let n := (BitVec.toNat Rn)
      if ((((m != n) || (d == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_CLZ_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_CMN_i_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2381.29-2381.30"
      let n := (BitVec.toNat Rn)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_CMN_i_Op_A_txt imm32 n))
  else (pure ())

def decode_aarch32_instrs_CMN_i_T1enc_A_txt (i : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_CMN_i_Op_A_txt imm32 n))
  else (pure ())

def decode_aarch32_instrs_CMN_r_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2440.29-2440.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_CMN_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_CMN_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_CMN_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_CMN_r_T2enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((n == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_CMN_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_CMN_rr_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2539.29-2539.30"
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((n == 15) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_CMN_rr_Op_A_txt m n s shift_t))
  else (pure ())

def decode_aarch32_instrs_CMP_i_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2580.29-2580.30"
      let n := (BitVec.toNat Rn)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_CMP_i_Op_A_txt imm32 n))
  else (pure ())

def decode_aarch32_instrs_CMP_i_T1enc_A_txt (Rn : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_CMP_i_Op_A_txt imm32 n))
  else (pure ())

def decode_aarch32_instrs_CMP_i_T2enc_A_txt (i : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_CMP_i_Op_A_txt imm32 n))
  else (pure ())

def decode_aarch32_instrs_CMP_r_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2657.29-2657.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_CMP_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_CMP_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_CMP_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_CMP_r_T2enc_A_txt (N : (BitVec 1)) (Rm : (BitVec 4)) (Rn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat (N +++ Rn))
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if (((n <b 8) && (m <b 8)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((n == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_CMP_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_CMP_r_T3enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((n == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_CMP_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_CMP_rr_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2787.29-2787.30"
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((n == 15) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_CMP_rr_Op_A_txt m n s shift_t))
  else (pure ())

def decode_aarch32_instrs_DBG_A1enc_A_txt (cond : (BitVec 4)) (option_name : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:2824.29-2824.30"
      (pure (execute_aarch32_instrs_DBG_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_DBG_T1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_DBG_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_DMB_A1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_DMB_Op_A_txt option_name)
  else (pure ())

def decode_aarch32_instrs_DMB_T1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_DMB_Op_A_txt option_name)
  else (pure ())

def decode_aarch32_instrs_DSB_A1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_DSB_Op_A_txt option_name)
  else (pure ())

def decode_aarch32_instrs_DSB_T1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_DSB_Op_A_txt option_name)
  else (pure ())

def decode_aarch32_instrs_EOR_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:3115.29-3115.30"
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (A32ExpandImm_C imm12 (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      (execute_aarch32_instrs_EOR_i_Op_A_txt carry d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_EOR_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "TEQ (immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (T32ExpandImm_C ((i +++ imm3) +++ imm8) (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      if ((((d == 15) && (! setflags)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_EOR_i_Op_A_txt carry d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_EOR_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:3199.29-3199.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_EOR_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_EOR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_EOR_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_EOR_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "TEQ (register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((((d == 15) && (! setflags)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_EOR_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_EOR_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:3311.29-3311.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_EOR_rr_Op_A_txt d m n s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_ISB_A1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_ISB_Op_A_txt ())
  else (pure ())

def decode_aarch32_instrs_ISB_T1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_ISB_Op_A_txt ())
  else (pure ())

def decode_aarch32_instrs_IT_T1enc_A_txt (firstcond : (BitVec 4)) (mask : (BitVec 4)) : SailM Unit := do
  if ((mask == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
  else (pure ())
  if (((firstcond == 0b1111#4) || ((firstcond == 0b1110#4) && ((BitCount mask) != 1))) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_IT_Op_A_txt firstcond mask)

def decode_aarch32_instrs_LDC_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:3431.29-3431.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDC (literal)")) : SailM Unit)
      else (pure ())
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let cp := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      (execute_aarch32_instrs_LDC_i_Op_A_txt add cp imm32 index n wback))
  else (pure ())

def decode_aarch32_instrs_LDC_i_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDC (literal)")) : SailM Unit)
      else (pure ())
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let cp := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      (execute_aarch32_instrs_LDC_i_Op_A_txt add cp imm32 index n wback))
  else (pure ())

def decode_aarch32_instrs_LDC_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:3507.29-3507.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let cp := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      if ((←((pure (W == 1#1)) <||> (do
           (pure (P == 0#1)) <&&> (do
             (pure (bne (← (CurrentInstrSet ())) InstrSet_A32)))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDC_l_Op_A_txt add cp imm32 index))
  else (pure ())

def decode_aarch32_instrs_LDC_l_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let cp := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      if ((←((pure (W == 1#1)) <||> (do
           (pure (P == 0#1)) <&&> (do
             (pure (bne (← (CurrentInstrSet ())) InstrSet_A32)))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDC_l_Op_A_txt add cp imm32 index))
  else (pure ())

def decode_aarch32_instrs_LDM_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:3589.29-3589.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDM_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_LDM_T1enc_A_txt (Rn : (BitVec 3)) (register_list : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := (0b00000000#8 +++ register_list)
      let wback : Bool := ((BitVec.join1 [(BitVec.access registers n)]) == 0#1)
      if (((BitCount registers) <b 1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDM_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_LDM_T2enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (P : (BitVec 1)) (M : (BitVec 1)) (register_list : (BitVec 14)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := ((P +++ M) +++ register_list)
      let wback : Bool := (W == 1#1)
      if ((((n == 15) || ((BitCount registers) <b 2)) || ((P == 1#1) && (M == 1#1))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access registers 13)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((BitVec.join1 [(BitVec.access registers 15)]) == 1#1)) <&&> (do
           (InITBlock ())) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDM_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_LDMDA_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:3697.29-3697.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDMDA_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_LDMDB_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:3749.29-3749.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDMDB_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_LDMDB_T1enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (P : (BitVec 1)) (M : (BitVec 1)) (register_list : (BitVec 14)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := ((P +++ M) +++ register_list)
      let wback : Bool := (W == 1#1)
      if ((((n == 15) || ((BitCount registers) <b 2)) || ((P == 1#1) && (M == 1#1))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access registers 13)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((BitVec.join1 [(BitVec.access registers 15)]) == 1#1)) <&&> (do
           (InITBlock ())) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDMDB_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_LDMIB_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:3835.29-3835.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDMIB_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_LDRB_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:3881.29-3881.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRB (literal)")) : SailM Unit)
      else (pure ())
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRBT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRB_i_OpA_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRB_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm5 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRB_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRB_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLD")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRB (literal)")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRB_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRB_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((((Rt == 0b1111#4) && (P == 1#1)) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "PLD, PLDW (immediate)")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRB (literal)")) : SailM Unit)
      else (pure ())
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "LDRBT")) : SailM Unit)
      else (pure ())
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((((t == 15) && (W == 1#1)) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRB_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRB_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4041.29-4041.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRBT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || wback) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRB_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDRB_l_T1enc_A_txt (U : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLD")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_LDRB_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDRB_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4114.29-4114.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRBT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRB_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRB_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_LDRB_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())


