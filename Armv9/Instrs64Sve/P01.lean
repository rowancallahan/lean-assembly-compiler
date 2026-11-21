import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.MonoRewrites
import Armv9.Prelude
import Armv9.Builtins
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, swsize : Nat, swsize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_REVH_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (swsize : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (← (Reverse element swsize))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, swsize : Nat, swsize = 8 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_REVB_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (swsize : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (← (Reverse element swsize))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UUNPKLO_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let hsize := (Int.ediv esize 2)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do
          if (hi : Bool)
          then (Elem_read operand (e +i elements) hsize)
          else (Elem_read operand e hsize) ) : SailM (BitVec hsize) )
        (Elem_set result e esize (← (Extend element esize is_unsigned)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UUNPKHI_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let hsize := (Int.ediv esize 2)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do
          if (hi : Bool)
          then (Elem_read operand (e +i elements) hsize)
          else (Elem_read operand e hsize) ) : SailM (BitVec hsize) )
        (Elem_set result e esize (← (Extend element esize is_unsigned)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUNPKLO_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let hsize := (Int.ediv esize 2)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do
          if (hi : Bool)
          then (Elem_read operand (e +i elements) hsize)
          else (Elem_read operand e hsize) ) : SailM (BitVec hsize) )
        (Elem_set result e esize (← (Extend element esize is_unsigned)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUNPKHI_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let hsize := (Int.ediv esize 2)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do
          if (hi : Bool)
          then (Elem_read operand (e +i elements) hsize)
          else (Elem_read operand e hsize) ) : SailM (BitVec hsize) )
        (Elem_set result e esize (← (Extend element esize is_unsigned)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, (is_VL VL) -/
def execute_SETFFR_F__ (VL : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  (FFR_set PL (Ones (n := PL)))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_setflags : Bool, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PTRUE_P_S__ (VL : Nat) (d : Nat) (esize : Nat) (pat : (BitVec 5)) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let pbit : (BitVec 1) :=
          if ((e <b count) : Bool)
          then 1#1
          else 0#1
        (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest result result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_setflags : Bool, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PTRUES_P_S__ (VL : Nat) (d : Nat) (esize : Nat) (pat : (BitVec 5)) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let pbit : (BitVec 1) :=
          if ((e <b count) : Bool)
          then 1#1
          else 0#1
        (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest result result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PFALSE_P__ (VL : Nat) (d : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  (P_set d PL (Zeros (n := PL)))

/-- Type quantifiers: VL : Nat, d : Nat, 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_RDFFR_P_F__ (VL : Nat) (d : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let ffr ← (( do (FFR_read PL) ) : SailM (BitVec PL) )
  (P_set d PL ffr)

/-- Type quantifiers: VL : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ (is_VL VL) -/
def execute_WRFFR_F_P__ (VL : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let hsb := (HighestSetBit operand)
  if (((hsb <b 0) || (is_ones_subrange operand hsb 0)) : Bool)
  then (FFR_set PL operand)
  else (FFR_set PL (← (__UNKNOWN_bits PL)))

/-- Type quantifiers: VL : Nat, d : Nat, g : Nat, k_setflags : Bool, 0 ≤ g ∧ g ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_RDFFR_P_P_F__ (VL : Nat) (d : Nat) (g : Nat) (setflags : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let ffr ← (( do (FFR_read PL) ) : SailM (BitVec PL) )
  let result : (BitVec PL) := (ffr &&& mask)
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result 8)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, g : Nat, k_setflags : Bool, 0 ≤ g ∧ g ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_RDFFRS_P_P_F__ (VL : Nat) (d : Nat) (g : Nat) (setflags : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let ffr ← (( do (FFR_read PL) ) : SailM (BitVec PL) )
  let result : (BitVec PL) := (ffr &&& mask)
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result 8)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_PTEST__P_P__ (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_merging : Bool, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKA_P_P_P__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (merging : Bool) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read d PL) ) : SailM (BitVec PL) )
  let break' : Bool := false
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let (break', result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (break', result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (break', result) := loop_vars
      loop_vars ← do
        let element ← (( do (ActivePredicateElement operand e esize) ) : SailM Bool )
        let (break', result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let pbit : (BitVec 1) :=
                if ((! break') : Bool)
                then 1#1
                else 0#1
              let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
              let break' : Bool := (break' || element)
              (pure (break', result)))
          else
            (do
              let result ← (( do
                if (merging : Bool)
                then
                  (do
                    let pbit ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
                    (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
                else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize))) ) : SailM (BitVec PL) )
              (pure (break', result))) ) : SailM (Bool × (BitVec PL)) )
        (pure (break', result))
    (pure loop_vars) ) : SailM (Bool × (BitVec PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_merging : Bool, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKAS_P_P_P_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (merging : Bool) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read d PL) ) : SailM (BitVec PL) )
  let break' : Bool := false
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let (break', result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (break', result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (break', result) := loop_vars
      loop_vars ← do
        let element ← (( do (ActivePredicateElement operand e esize) ) : SailM Bool )
        let (break', result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let pbit : (BitVec 1) :=
                if ((! break') : Bool)
                then 1#1
                else 0#1
              let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
              let break' : Bool := (break' || element)
              (pure (break', result)))
          else
            (do
              let result ← (( do
                if (merging : Bool)
                then
                  (do
                    let pbit ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
                    (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
                else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize))) ) : SailM (BitVec PL) )
              (pure (break', result))) ) : SailM (Bool × (BitVec PL)) )
        (pure (break', result))
    (pure loop_vars) ) : SailM (Bool × (BitVec PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_merging : Bool, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKB_P_P_P__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (merging : Bool) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read d PL) ) : SailM (BitVec PL) )
  let break' : Bool := false
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let (break', result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (break', result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (break', result) := loop_vars
      loop_vars ← do
        let element ← (( do (ActivePredicateElement operand e esize) ) : SailM Bool )
        let (break', result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let break' : Bool := (break' || element)
              let pbit : (BitVec 1) :=
                if ((! break') : Bool)
                then 1#1
                else 0#1
              let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
              (pure (break', result)))
          else
            (do
              let result ← (( do
                if (merging : Bool)
                then
                  (do
                    let pbit ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
                    (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
                else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize))) ) : SailM (BitVec PL) )
              (pure (break', result))) ) : SailM (Bool × (BitVec PL)) )
        (pure (break', result))
    (pure loop_vars) ) : SailM (Bool × (BitVec PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_merging : Bool, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKBS_P_P_P_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (merging : Bool) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read d PL) ) : SailM (BitVec PL) )
  let break' : Bool := false
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let (break', result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (break', result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (break', result) := loop_vars
      loop_vars ← do
        let element ← (( do (ActivePredicateElement operand e esize) ) : SailM Bool )
        let (break', result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let break' : Bool := (break' || element)
              let pbit : (BitVec 1) :=
                if ((! break') : Bool)
                then 1#1
                else 0#1
              let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
              (pure (break', result)))
          else
            (do
              let result ← (( do
                if (merging : Bool)
                then
                  (do
                    let pbit ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
                    (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
                else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize))) ) : SailM (BitVec PL) )
              (pure (break', result))) ) : SailM (Bool × (BitVec PL)) )
        (pure (break', result))
    (pure loop_vars) ) : SailM (Bool × (BitVec PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_AND_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (element1 &&& element2) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_ANDS_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (element1 &&& element2) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BIC_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (element1 &&& (Complement.complement element2)) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BICS_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (element1 &&& (Complement.complement element2)) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_EOR_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (element1 ^^^ element2) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_EORS_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (element1 ^^^ element2) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_NAND_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (Complement.complement (element1 &&& element2)) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_NANDS_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (Complement.complement (element1 &&& element2)) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_NOR_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (Complement.complement (element1 ||| element2)) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_NORS_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (Complement.complement (element1 ||| element2)) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_ORN_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (element1 ||| (Complement.complement element2)) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_ORNS_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (element1 ||| (Complement.complement element2)) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_ORR_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (element1 ||| element2) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_ORRS_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend (element1 ||| element2) psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_SEL_P_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
        let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend element1 psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend element2 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 15 ∧ (is_VL VL) -/
def execute_PFIRST_P_P_P__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (P_read dn PL) ) : SailM (BitVec PL) )
  let first : Int := (Neg.neg 1)
  let psize := (Int.ediv esize 8)
  let first ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := first
    for e in [loop_e_lower:loop_e_upper:1]i do
      let first := loop_vars
      loop_vars ← do
        if (((← (ActivePredicateElement mask e esize)) && (first == (Neg.neg 1))) : Bool)
        then (pure e)
        else (pure first)
    (pure loop_vars) ) : SailM Int )
  let first := first
  let result ← (( do
    if ((first ≥b 0) : Bool)
    then (do (Elem_set result first psize (Sail.BitVec.zeroExtend 1#1 psize)))
    else (pure result) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set dn PL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, v : Nat, 0 ≤ v ∧ v ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 15 ∧ (is_VL VL) -/
def execute_PNEXT_P_P_P__ (VL : Nat) (dn : Nat) (esize : Nat) (v : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read v PL) ) : SailM (BitVec PL) )
  let operand ← (( do (P_read dn PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let next ← (( do (pure ((← (LastActiveElement operand esize)) +i 1)) ) : SailM Int )
  let next ← (( do
    let mut loop_vars := next
    while (← (λ next => do (pure (next <b elements)) <&&> (do (pure (! (← (ActivePredicateElement mask next esize)))))) loop_vars) do
      let next := loop_vars
      loop_vars := ((next +i 1) : Int)
    (pure loop_vars) ) : SailM Int )
  let next := next
  let result : (BitVec PL) := (Zeros (n := PL))
  let result ← (( do
    if ((next <b elements) : Bool)
    then (do (Elem_set result next psize (Sail.BitVec.zeroExtend 1#1 psize)))
    else (pure result) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set dn PL result)

/-- Type quantifiers: VL : Nat, d : Nat, imm : Int, 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_RDVL_R_I__ (VL : Nat) (d : Nat) (imm : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let len := (imm *i (Int.ediv VL 8))
  (X_set d 64 (integer_subrange len 63 0))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, v : Nat, 0 ≤ v ∧ v ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SEL_Z_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (v : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read v PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement (Complement.complement mask) esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
        else (do (Elem_set result e esize (← (Elem_read operand2 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LSL_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize (element1 <<< shift))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LSR_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize (element1 >>> shift))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ASR_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize (BitVec.sshiftRight element1 shift))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, shift : Int, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ASRD_Z_P_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element1 ← (( do (pure (BitVec.toInt (← (Elem_read operand1 e esize)))) ) : SailM Int )
            let element1 : Int :=
              if ((element1 <b 0) : Bool)
              then (element1 +i ((_shl_int_general 1 shift) -i 1))
              else element1
            let element1 := element1
            (Elem_set result e esize (integer_subrange (_shr_int_general element1 shift) (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, shift : Int, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_LSL_Z_P_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let PL := (Int.ediv VL 8)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (element1 <<< shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, shift : Int, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_LSR_Z_P_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let PL := (Int.ediv VL 8)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (element1 >>> shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, shift : Int, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ASR_Z_P_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let PL := (Int.ediv VL 8)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (BitVec.sshiftRight element1 shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LSL_Z_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 (Int.ediv (e *i esize) 64) 64) ) : SailM (BitVec 64) )
        let shift := (Min.min (BitVec.toNat element2) esize)
        (Elem_set result e esize (element1 <<< shift))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LSR_Z_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 (Int.ediv (e *i esize) 64) 64) ) : SailM (BitVec 64) )
        let shift := (Min.min (BitVec.toNat element2) esize)
        (Elem_set result e esize (element1 >>> shift))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ASR_Z_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 (Int.ediv (e *i esize) 64) 64) ) : SailM (BitVec 64) )
        let shift := (Min.min (BitVec.toNat element2) esize)
        (Elem_set result e esize (BitVec.sshiftRight element1 shift))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_LSL_Z_P_ZW__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 (Int.ediv (e *i esize) 64) 64) ) : SailM (BitVec 64) )
            let shift := (Min.min (BitVec.toNat element2) esize)
            (Elem_set result e esize (element1 <<< shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_LSR_Z_P_ZW__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 (Int.ediv (e *i esize) 64) 64) ) : SailM (BitVec 64) )
            let shift := (Min.min (BitVec.toNat element2) esize)
            (Elem_set result e esize (element1 >>> shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ASR_Z_P_ZW__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 (Int.ediv (e *i esize) 64) 64) ) : SailM (BitVec 64) )
            let shift := (Min.min (BitVec.toNat element2) esize)
            (Elem_set result e esize (BitVec.sshiftRight element1 shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ABS_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (pure (BitVec.toInt (← (Elem_read operand e esize)))) ) : SailM Int )
            let element := (Int.natAbs element)
            (Elem_set result e esize (integer_subrange element (esize -i 1) 0)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CLS_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (integer_subrange (CountLeadingSignBits element) (esize -i 1) 0)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CLZ_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (integer_subrange (CountLeadingZeroBits element) (esize -i 1) 0)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CNOT_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend (IsZeroBit element) esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CNT_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (integer_subrange (BitCount element) (esize -i 1) 0)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FABS_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:33028.53-33028.54"
            (Elem_set result e esize (← (FPAbs element))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FNEG_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:33097.53-33097.54"
            (Elem_set result e esize (← (FPNeg element))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_NEG_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (pure (BitVec.toInt (← (Elem_read operand e esize)))) ) : SailM Int )
            let element := (Neg.neg element)
            (Elem_set result e esize (integer_subrange element (esize -i 1) 0)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_NOT_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (Complement.complement element)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_RBIT_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (← (BitReverse element))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQADD_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element1 +i element2) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQADD_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element1 +i element2) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQSUB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element1 -i element2) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQSUB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element1 -i element2) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQADD_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element1 +i imm) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQADD_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element1 +i imm) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQSUB_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element1 -i imm) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQSUB_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element1 -i imm) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKPA_P_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last ← (( do (pure ((← (LastActive mask operand1 8)) == 1#1)) ) : SailM Bool )
  let (last, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (last, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (last, result) := loop_vars
      loop_vars ← do
        let (last, result) ← (( do
          if ((← (ActivePredicateElement mask e 8)) : Bool)
          then
            (do
              let pbit : (BitVec 1) :=
                if (last : Bool)
                then 1#1
                else 0#1
              let result ← (Elem_set result e 1 (Sail.BitVec.zeroExtend pbit 1))
              let last ← (pure last) <&&> (do (pure (! (← (ActivePredicateElement operand2 e 8)))))
              (pure (last, result)))
          else
            (do
              let result ← (Elem_set result e 1 (Sail.BitVec.zeroExtend 0#1 1))
              (pure (last, result))) ) : SailM (Bool × (BitVec PL)) )
        (pure (last, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKPAS_P_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last ← (( do (pure ((← (LastActive mask operand1 8)) == 1#1)) ) : SailM Bool )
  let (last, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (last, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (last, result) := loop_vars
      loop_vars ← do
        let (last, result) ← (( do
          if ((← (ActivePredicateElement mask e 8)) : Bool)
          then
            (do
              let pbit : (BitVec 1) :=
                if (last : Bool)
                then 1#1
                else 0#1
              let result ← (Elem_set result e 1 (Sail.BitVec.zeroExtend pbit 1))
              let last ← (pure last) <&&> (do (pure (! (← (ActivePredicateElement operand2 e 8)))))
              (pure (last, result)))
          else
            (do
              let result ← (Elem_set result e 1 (Sail.BitVec.zeroExtend 0#1 1))
              (pure (last, result))) ) : SailM (Bool × (BitVec PL)) )
        (pure (last, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKPB_P_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last ← (( do (pure ((← (LastActive mask operand1 8)) == 1#1)) ) : SailM Bool )
  let (last, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (last, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (last, result) := loop_vars
      loop_vars ← do
        let (last, result) ← (( do
          if ((← (ActivePredicateElement mask e 8)) : Bool)
          then
            (do
              let last ← (pure last) <&&> (do (pure (! (← (ActivePredicateElement operand2 e 8)))))
              let pbit : (BitVec 1) :=
                if (last : Bool)
                then 1#1
                else 0#1
              let result ← (Elem_set result e 1 (Sail.BitVec.zeroExtend pbit 1))
              (pure (last, result)))
          else
            (do
              let result ← (Elem_set result e 1 (Sail.BitVec.zeroExtend 0#1 1))
              (pure (last, result))) ) : SailM (Bool × (BitVec PL)) )
        (pure (last, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKPBS_P_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last ← (( do (pure ((← (LastActive mask operand1 8)) == 1#1)) ) : SailM Bool )
  let (last, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (last, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (last, result) := loop_vars
      loop_vars ← do
        let (last, result) ← (( do
          if ((← (ActivePredicateElement mask e 8)) : Bool)
          then
            (do
              let last ← (pure last) <&&> (do (pure (! (← (ActivePredicateElement operand2 e 8)))))
              let pbit : (BitVec 1) :=
                if (last : Bool)
                then 1#1
                else 0#1
              let result ← (Elem_set result e 1 (Sail.BitVec.zeroExtend pbit 1))
              (pure (last, result)))
          else
            (do
              let result ← (Elem_set result e 1 (Sail.BitVec.zeroExtend 0#1 1))
              (pure (last, result))) ) : SailM (Bool × (BitVec PL)) )
        (pure (last, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest mask result esize)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, dm : Nat, g : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ 0 ≤ dm ∧ dm ≤ 15 ∧ (is_VL VL) -/
def execute_BRKN_P_P_PP__ (VL : Nat) (dm : Nat) (g : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read dm PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let result ← (( do
    if (((← (LastActive mask operand1 8)) == 1#1) : Bool)
    then (pure operand2)
    else (pure (Zeros (n := PL))) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest (Ones (n := PL)) result 8)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set dm PL result)

/-- Type quantifiers: VL : Nat, dm : Nat, g : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ 0 ≤ dm ∧ dm ≤ 15 ∧ (is_VL VL) -/
def execute_BRKNS_P_P_PP__ (VL : Nat) (dm : Nat) (g : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read dm PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let result ← (( do
    if (((← (LastActive mask operand1 8)) == 1#1) : Bool)
    then (pure operand2)
    else (pure (Zeros (n := PL))) ) : SailM (BitVec PL) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← do (PredTest (Ones (n := PL)) result 8)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  (P_set dm PL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INSR_Z_V__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dest ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let src ← (( do (V_read m esize) ) : SailM (BitVec esize) )
  (Z_set dn VL ((Sail.BitVec.extractLsb dest ((VL -i esize) -i 1) 0) +++ src))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INSR_Z_R__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dest ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let src ← (( do (X_read m esize) ) : SailM (BitVec esize) )
  (Z_set dn VL ((Sail.BitVec.extractLsb dest ((VL -i esize) -i 1) 0) +++ src))

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SDOT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
              let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SDOT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
              let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SDOT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
              let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UDOT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
              let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UDOT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
              let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UDOT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
              let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_USDOT_Z_ZZZ_S (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
              let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_USDOT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
              let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SUDOT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
              let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SDOT_Z32_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
              let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SDOT_Z32_ZZZi__ (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
              let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i i) (Int.ediv esize 2)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UDOT_Z32_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
              let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UDOT_Z32_ZZZi__ (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
              let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i i) (Int.ediv esize 2)))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQABS_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (pure (BitVec.toInt (← (Elem_read operand e esize)))) ) : SailM Int )
            let element := (Int.natAbs element)
            (Elem_set result e esize (← (SignedSat element esize))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQNEG_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (pure (BitVec.toInt (← (Elem_read operand e esize)))) ) : SailM Int )
            let element := (Neg.neg element)
            (Elem_set result e esize (← (SignedSat element esize))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULH_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e esize (← (SignedSat (Int.shiftr res esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMULH_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLAH_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let res := ((Int.shiftl element3 esize) +i ((2 *i element1) *i element2))
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLSH_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let res := ((Int.shiftl element3 esize) -i ((2 *i element1) *i element2))
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ADDP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2, result) ← (( do
          if ((! (← (ActivePredicateElement mask e esize))) : Bool)
          then
            (do
              let result ← (Elem_set result e esize (← (Elem_read operand1 e esize)))
              (pure (element1, element2, result)))
          else
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let element1 ← (pure (BitVec.toNat (← (Elem_read operand1 (e +i 0) esize))))
                    let element2 ← (pure (BitVec.toNat (← (Elem_read operand1 (e +i 1) esize))))
                    (pure (element1, element2)))
                else
                  (do
                    let element1 ← (pure (BitVec.toNat (← (Elem_read operand2 (e -i 1) esize))))
                    let element2 ← (pure (BitVec.toNat (← (Elem_read operand2 (e +i 0) esize))))
                    (pure (element1, element2))) ) : SailM (Int × Int) )
              let res := (element1 +i element2)
              let result ← (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
              (pure (element1, element2, result))) ) : SailM (Int × Int × (BitVec VL)) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAXP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2, result) ← (( do
          if ((! (← (ActivePredicateElement mask e esize))) : Bool)
          then
            (do
              let result ← (Elem_set result e esize (← (Elem_read operand1 e esize)))
              (pure (element1, element2, result)))
          else
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let element1 ← (pure (BitVec.toNat (← (Elem_read operand1 (e +i 0) esize))))
                    let element2 ← (pure (BitVec.toNat (← (Elem_read operand1 (e +i 1) esize))))
                    (pure (element1, element2)))
                else
                  (do
                    let element1 ← (pure (BitVec.toNat (← (Elem_read operand2 (e -i 1) esize))))
                    let element2 ← (pure (BitVec.toNat (← (Elem_read operand2 (e +i 0) esize))))
                    (pure (element1, element2))) ) : SailM (Int × Int) )
              let res := (Max.max element1 element2)
              let result ← (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
              (pure (element1, element2, result))) ) : SailM (Int × Int × (BitVec VL)) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAXP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2, result) ← (( do
          if ((! (← (ActivePredicateElement mask e esize))) : Bool)
          then
            (do
              let result ← (Elem_set result e esize (← (Elem_read operand1 e esize)))
              (pure (element1, element2, result)))
          else
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 (e +i 0) esize))))
                    let element2 ← (pure (BitVec.toInt (← (Elem_read operand1 (e +i 1) esize))))
                    (pure (element1, element2)))
                else
                  (do
                    let element1 ← (pure (BitVec.toInt (← (Elem_read operand2 (e -i 1) esize))))
                    let element2 ← (pure (BitVec.toInt (← (Elem_read operand2 (e +i 0) esize))))
                    (pure (element1, element2))) ) : SailM (Int × Int) )
              let res := (Max.max element1 element2)
              let result ← (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
              (pure (element1, element2, result))) ) : SailM (Int × Int × (BitVec VL)) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMINP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2, result) ← (( do
          if ((! (← (ActivePredicateElement mask e esize))) : Bool)
          then
            (do
              let result ← (Elem_set result e esize (← (Elem_read operand1 e esize)))
              (pure (element1, element2, result)))
          else
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let element1 ← (pure (BitVec.toNat (← (Elem_read operand1 (e +i 0) esize))))
                    let element2 ← (pure (BitVec.toNat (← (Elem_read operand1 (e +i 1) esize))))
                    (pure (element1, element2)))
                else
                  (do
                    let element1 ← (pure (BitVec.toNat (← (Elem_read operand2 (e -i 1) esize))))
                    let element2 ← (pure (BitVec.toNat (← (Elem_read operand2 (e +i 0) esize))))
                    (pure (element1, element2))) ) : SailM (Int × Int) )
              let res := (Min.min element1 element2)
              let result ← (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
              (pure (element1, element2, result))) ) : SailM (Int × Int × (BitVec VL)) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMINP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2, result) ← (( do
          if ((! (← (ActivePredicateElement mask e esize))) : Bool)
          then
            (do
              let result ← (Elem_set result e esize (← (Elem_read operand1 e esize)))
              (pure (element1, element2, result)))
          else
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 (e +i 0) esize))))
                    let element2 ← (pure (BitVec.toInt (← (Elem_read operand1 (e +i 1) esize))))
                    (pure (element1, element2)))
                else
                  (do
                    let element1 ← (pure (BitVec.toInt (← (Elem_read operand2 (e -i 1) esize))))
                    let element2 ← (pure (BitVec.toInt (← (Elem_read operand2 (e +i 0) esize))))
                    (pure (element1, element2))) ) : SailM (Int × Int) )
              let res := (Min.min element1 element2)
              let result ← (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
              (pure (element1, element2, result))) ) : SailM (Int × Int × (BitVec VL)) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SADALP_Z_P_Z__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand_acc ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let operand_src ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((! (← (ActivePredicateElement mask e esize))) : Bool)
        then (do (Elem_set result e esize (← (Elem_read operand_acc e esize))))
        else
          (do
            let element1 ← do (pure (BitVec.toInt (← (Elem_read operand_src ((2 *i e) +i 0) (Int.ediv esize 2)))))
            let element2 ← do (pure (BitVec.toInt (← (Elem_read operand_src ((2 *i e) +i 1) (Int.ediv esize 2)))))
            let sum : (BitVec esize) := (integer_subrange (element1 +i element2) (esize -i 1) 0)
            (Elem_set result e esize ((← (Elem_read operand_acc e esize)) + sum)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UADALP_Z_P_Z__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand_acc ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let operand_src ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((! (← (ActivePredicateElement mask e esize))) : Bool)
        then (do (Elem_set result e esize (← (Elem_read operand_acc e esize))))
        else
          (do
            let element1 ← do (pure (BitVec.toNat (← (Elem_read operand_src ((2 *i e) +i 0) (Int.ediv esize 2)))))
            let element2 ← do (pure (BitVec.toNat (← (Elem_read operand_src ((2 *i e) +i 1) (Int.ediv esize 2)))))
            let sum : (BitVec esize) := (integer_subrange (element1 +i element2) (esize -i 1) 0)
            (Elem_set result e esize ((← (Elem_read operand_acc e esize)) + sum)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SHRNB_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general (BitVec.toNat element) shift)
        let result ← (Elem_set result ((2 *i e) +i 0) esize (integer_subrange res (esize -i 1) 0))
        (Elem_set result ((2 *i e) +i 1) esize (Zeros (n := esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SHRNT_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general (BitVec.toNat element) shift)
        (Elem_set result ((2 *i e) +i 1) esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_RSHRNB_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1))) shift)
        let result ← (Elem_set result ((2 *i e) +i 0) esize (integer_subrange res (esize -i 1) 0))
        (Elem_set result ((2 *i e) +i 1) esize (Zeros (n := esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_RSHRNT_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1))) shift)
        (Elem_set result ((2 *i e) +i 1) esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQSHRNB_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general (BitVec.toInt element) shift)
        let result ← (Elem_set result ((2 *i e) +i 0) esize (← (SignedSat res esize)))
        (Elem_set result ((2 *i e) +i 1) esize (Zeros (n := esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQSHRNT_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general (BitVec.toInt element) shift)
        (Elem_set result ((2 *i e) +i 1) esize (← (SignedSat res esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQSHRNB_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general (BitVec.toNat element) shift)
        let result ← (Elem_set result ((2 *i e) +i 0) esize (← (UnsignedSat res esize)))
        (Elem_set result ((2 *i e) +i 1) esize (Zeros (n := esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQSHRNT_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general (BitVec.toNat element) shift)
        (Elem_set result ((2 *i e) +i 1) esize (← (UnsignedSat res esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRNB_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
        let result ← (Elem_set result ((2 *i e) +i 0) esize (← (SignedSat res esize)))
        (Elem_set result ((2 *i e) +i 1) esize (Zeros (n := esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRNT_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
        (Elem_set result ((2 *i e) +i 1) esize (← (SignedSat res esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHRNB_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1))) shift)
        let result ← (Elem_set result ((2 *i e) +i 0) esize (← (UnsignedSat res esize)))
        (Elem_set result ((2 *i e) +i 1) esize (Zeros (n := esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHRNT_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1))) shift)
        (Elem_set result ((2 *i e) +i 1) esize (← (UnsignedSat res esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQSHRUNB_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general (BitVec.toInt element) shift)
        let result ← (Elem_set result ((2 *i e) +i 0) esize (← (UnsignedSat res esize)))
        (Elem_set result ((2 *i e) +i 1) esize (Zeros (n := esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQSHRUNT_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general (BitVec.toInt element) shift)
        (Elem_set result ((2 *i e) +i 1) esize (← (UnsignedSat res esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRUNB_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
        let result ← (Elem_set result ((2 *i e) +i 0) esize (← (UnsignedSat res esize)))
        (Elem_set result ((2 *i e) +i 1) esize (Zeros (n := esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRUNT_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
        let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
        (Elem_set result ((2 *i e) +i 1) esize (← (UnsignedSat res esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, shift : Int, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SRSHR_Z_P_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (_shr_int_general (element1 +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, shift : Int, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_URSHR_Z_P_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (_shr_int_general (element1 +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, shift : Int, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQSHL_Z_P_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (_shl_int_general element1 shift)
            (Elem_set result e esize (← (SignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, shift : Int, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQSHL_Z_P_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (_shl_int_general element1 shift)
            (Elem_set result e esize (← (UnsignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, shift : Int, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQSHLU_Z_P_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (_shl_int_general element1 shift)
            (Elem_set result e esize (← (UnsignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SSHLLB_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand ((2 *i e) +i 0) esize) ) : SailM (BitVec esize) )
        let shifted_value := (_shl_int_general (BitVec.toInt element) shift)
        (Elem_set result e (2 *i esize) (integer_subrange shifted_value ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SSHLLT_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand ((2 *i e) +i 1) esize) ) : SailM (BitVec esize) )
        let shifted_value := (_shl_int_general (BitVec.toInt element) shift)
        (Elem_set result e (2 *i esize) (integer_subrange shifted_value ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_USHLLB_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand ((2 *i e) +i 0) esize) ) : SailM (BitVec esize) )
        let shifted_value := (_shl_int_general (BitVec.toNat element) shift)
        (Elem_set result e (2 *i esize) (integer_subrange shifted_value ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_USHLLT_Z_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand ((2 *i e) +i 1) esize) ) : SailM (BitVec esize) )
        let shifted_value := (_shl_int_general (BitVec.toNat element) shift)
        (Elem_set result e (2 *i esize) (integer_subrange shifted_value ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQXTNB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let res ← (( do (SignedSat element1 halfesize) ) : SailM (BitVec halfesize) )
        let result ← (Elem_set result ((2 *i e) +i 0) halfesize res)
        (Elem_set result ((2 *i e) +i 1) halfesize (Zeros (n := halfesize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQXTNB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let res ← (( do (UnsignedSat element1 halfesize) ) : SailM (BitVec halfesize) )
        let result ← (Elem_set result ((2 *i e) +i 0) halfesize res)
        (Elem_set result ((2 *i e) +i 1) halfesize (Zeros (n := halfesize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQXTUNB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let res ← (( do (UnsignedSat element1 halfesize) ) : SailM (BitVec halfesize) )
        let result ← (Elem_set result ((2 *i e) +i 0) halfesize res)
        (Elem_set result ((2 *i e) +i 1) halfesize (Zeros (n := halfesize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQXTNT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let res ← (( do (SignedSat element1 halfesize) ) : SailM (BitVec halfesize) )
        (Elem_set result ((2 *i e) +i 1) halfesize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQXTNT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let res ← (( do (UnsignedSat element1 halfesize) ) : SailM (BitVec halfesize) )
        (Elem_set result ((2 *i e) +i 1) halfesize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQXTUNT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let res ← (( do (UnsignedSat element1 halfesize) ) : SailM (BitVec halfesize) )
        (Elem_set result ((2 *i e) +i 1) halfesize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMULLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let res := (element1 *i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMULLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let res := (element1 *i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMULLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let res := (element1 *i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMULLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let res := (element1 *i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e esize (← (SignedSat res esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e esize (← (SignedSat res esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLALT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLALB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLALT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLALB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLALT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2)))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e esize))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) esize))))
        (Elem_set result e esize (← (SignedSat (element3 +i product) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 0 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLALB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2)))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e esize))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) esize))))
        (Elem_set result e esize (← (SignedSat (element3 +i product) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLSLT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLSLB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLSLT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLSLB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLSLT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2)))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e esize))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) esize))))
        (Elem_set result e esize (← (SignedSat (element3 -i product) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 0 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLSLB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2)))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e esize))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) esize))))
        (Elem_set result e esize (← (SignedSat (element3 -i product) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SABALT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let absdiff : (BitVec esize) := (integer_subrange (Int.natAbs (element1 -i element2)) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + absdiff))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SABALB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let absdiff : (BitVec esize) := (integer_subrange (Int.natAbs (element1 -i element2)) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + absdiff))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UABALT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let absdiff : (BitVec esize) := (integer_subrange (Int.natAbs (element1 -i element2)) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + absdiff))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UABALB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let absdiff : (BitVec esize) := (integer_subrange (Int.natAbs (element1 -i element2)) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + absdiff))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SABA_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let absdiff : (BitVec esize) := (integer_subrange (Int.natAbs (element1 -i element2)) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + absdiff))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UABA_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let absdiff : (BitVec esize) := (integer_subrange (Int.natAbs (element1 -i element2)) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + absdiff))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SADDWT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        (Elem_set result e esize (integer_subrange (element1 +i element2) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SADDWB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        (Elem_set result e esize (integer_subrange (element1 +i element2) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UADDWT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        (Elem_set result e esize (integer_subrange (element1 +i element2) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UADDWB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        (Elem_set result e esize (integer_subrange (element1 +i element2) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SSUBWT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        (Elem_set result e esize (integer_subrange (element1 -i element2) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SSUBWB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        (Elem_set result e esize (integer_subrange (element1 -i element2) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_USUBWT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        (Elem_set result e esize (integer_subrange (element1 -i element2) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_USUBWB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        (Elem_set result e esize (integer_subrange (element1 -i element2) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMUL_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize (Sail.BitVec.extractLsb (PolynomialMult element1 element2) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMULLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (PolynomialMult element1 element2))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMULLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (PolynomialMult element1 element2))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMULLT_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (PolynomialMult element1 element2))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMULLB_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (PolynomialMult element1 element2))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQSHL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general element shift))
            let res := res
            (Elem_set result e esize (← (SignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQSHL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general element shift))
            let res := res
            (Elem_set result e esize (← (UnsignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SRSHL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
            let res := res
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_URSHL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
            let res := res
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
            let res := res
            (Elem_set result e esize (← (SignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
            let res := res
            (Elem_set result e esize (← (UnsignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQSHLR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general element shift))
            let res := res
            (Elem_set result e esize (← (SignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand2 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQSHLR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general element shift))
            let res := res
            (Elem_set result e esize (← (UnsignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand2 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SRSHLR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
            let res := res
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand2 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_URSHLR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
            let res := res
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand2 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHLR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
            let res := res
            (Elem_set result e esize (← (SignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand2 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHLR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let shift ← (( do (pure (ShiftSat (BitVec.toInt (← (Elem_read operand2 e esize))) esize)) ) : SailM Int )
            let res ← (( do (undefined_int ()) ) : SailM Int )
            let res : Int :=
              if ((shift ≥b 0) : Bool)
              then (_shl_int_general element shift)
              else
                (let shift := (Neg.neg shift)
                (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
            let res := res
            (Elem_set result e esize (← (UnsignedSat res esize))))
        else (do (Elem_set result e esize (← (Elem_read operand2 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADDHNB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        let res := (Int.shiftr (element1 +i element2) halfesize)
        let result ← (Elem_set result ((2 *i e) +i 0) halfesize (integer_subrange res (halfesize -i 1) 0))
        (Elem_set result ((2 *i e) +i 1) halfesize (Zeros (n := halfesize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADDHNT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        let res := (Int.shiftr (element1 +i element2) halfesize)
        (Elem_set result ((2 *i e) +i 1) halfesize (integer_subrange res (halfesize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUBHNB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        let res := (Int.shiftr (element1 -i element2) halfesize)
        let result ← (Elem_set result ((2 *i e) +i 0) halfesize (integer_subrange res (halfesize -i 1) 0))
        (Elem_set result ((2 *i e) +i 1) halfesize (Zeros (n := halfesize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUBHNT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        let res := (Int.shiftr (element1 -i element2) halfesize)
        (Elem_set result ((2 *i e) +i 1) halfesize (integer_subrange res (halfesize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_RADDHNB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        let res := (Int.shiftr ((element1 +i element2) +i (Int.shiftl 1 (halfesize -i 1))) halfesize)
        let result ← (Elem_set result ((2 *i e) +i 0) halfesize (integer_subrange res (halfesize -i 1) 0))
        (Elem_set result ((2 *i e) +i 1) halfesize (Zeros (n := halfesize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_RADDHNT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        let res := (Int.shiftr ((element1 +i element2) +i (Int.shiftl 1 (halfesize -i 1))) halfesize)
        (Elem_set result ((2 *i e) +i 1) halfesize (integer_subrange res (halfesize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_RSUBHNB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        let res := (Int.shiftr ((element1 -i element2) +i (Int.shiftl 1 (halfesize -i 1))) halfesize)
        let result ← (Elem_set result ((2 *i e) +i 0) halfesize (integer_subrange res (halfesize -i 1) 0))
        (Elem_set result ((2 *i e) +i 1) halfesize (Zeros (n := halfesize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_RSUBHNT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let halfesize := (Int.ediv esize 2)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        let res := (Int.shiftr ((element1 -i element2) +i (Int.shiftl 1 (halfesize -i 1))) halfesize)
        (Elem_set result ((2 *i e) +i 1) halfesize (integer_subrange res (halfesize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SABDLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let res := (Int.natAbs (element1 -i element2))
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SABDLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let res := (Int.natAbs (element1 -i element2))
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UABDLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)))))
        let res := (Int.natAbs (element1 -i element2))
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UABDLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)))))
        let res := (Int.natAbs (element1 -i element2))
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 0 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SADDLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 +i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SADDLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 +i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 0 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SSUBLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 -i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SSUBLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 -i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 0 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UADDLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 +i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UADDLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 +i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 0 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_USUBLB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 -i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_USUBLT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 -i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SADDLBT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 +i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SSUBLBT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 -i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 0 ∧ sel1 = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SSUBLTB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2))) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2))) is_unsigned)
        let res := (element1 -i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, k_sub_i : Bool, k_sub_r : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_CADD_Z_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let acc_r ← (( do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i p) +i 0) esize)))) ) : SailM Int )
        let acc_i ← (( do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i p) +i 1) esize)))) ) : SailM Int )
        let elt2_r ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i p) +i 0) esize))))
        let elt2_i ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i p) +i 1) esize))))
        let (acc_i, acc_r) : (Int × Int) :=
          if (sub_i : Bool)
          then
            (let acc_r : Int := (acc_r -i elt2_i)
            let acc_i : Int := (acc_i +i elt2_r)
            (acc_i, acc_r))
          else (acc_i, acc_r)
        let (acc_i, acc_r) : (Int × Int) :=
          if (sub_r : Bool)
          then
            (let acc_r : Int := (acc_r +i elt2_i)
            let acc_i : Int := (acc_i -i elt2_r)
            (acc_i, acc_r))
          else (acc_i, acc_r)
        let acc_r := acc_r
        let acc_i := acc_i
        let result ← (Elem_set result ((2 *i p) +i 0) esize (integer_subrange acc_r (esize -i 1) 0))
        (Elem_set result ((2 *i p) +i 1) esize (integer_subrange acc_i (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, k_sub_i : Bool, k_sub_r : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQCADD_Z_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let acc_r ← (( do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i p) +i 0) esize)))) ) : SailM Int )
        let acc_i ← (( do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i p) +i 1) esize)))) ) : SailM Int )
        let elt2_r ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i p) +i 0) esize))))
        let elt2_i ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i p) +i 1) esize))))
        let (acc_i, acc_r) : (Int × Int) :=
          if (sub_i : Bool)
          then
            (let acc_r : Int := (acc_r -i elt2_i)
            let acc_i : Int := (acc_i +i elt2_r)
            (acc_i, acc_r))
          else (acc_i, acc_r)
        let (acc_i, acc_r) : (Int × Int) :=
          if (sub_r : Bool)
          then
            (let acc_r : Int := (acc_r +i elt2_i)
            let acc_i : Int := (acc_i -i elt2_r)
            (acc_i, acc_r))
          else (acc_i, acc_r)
        let acc_r := acc_r
        let acc_i := acc_i
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (SignedSat acc_r esize)))
        (Elem_set result ((2 *i p) +i 1) esize (← (SignedSat acc_i esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i : Bool, k_sub_r : Bool, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let elt1_a ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i p) +i sel_a) esize))))
        let elt2_a ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i p) +i sel_a) esize))))
        let elt2_b ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i p) +i sel_b) esize))))
        let elt3_r ← (( do (Elem_read operand3 ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let elt3_i ← (( do (Elem_read operand3 ((2 *i p) +i 1) esize) ) : SailM (BitVec esize) )
        let product_r := (elt1_a *i elt2_a)
        let product_i := (elt1_a *i elt2_b)
        let result ← (( do
          if (sub_r : Bool)
          then (do (Elem_set result ((2 *i p) +i 0) esize (BitVec.subInt elt3_r product_r)))
          else (do (Elem_set result ((2 *i p) +i 0) esize (BitVec.addInt elt3_r product_r))) ) : SailM (BitVec VL) )
        if (sub_i : Bool)
        then (do (Elem_set result ((2 *i p) +i 1) esize (BitVec.subInt elt3_i product_i)))
        else (do (Elem_set result ((2 *i p) +i 1) esize (BitVec.addInt elt3_i product_i)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i : Bool, k_sub_r : Bool, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CMLA_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let pairspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (p -i (Nat.mod p pairspersegment))
        let s := (segmentbase +i index)
        let elt1_a ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i p) +i sel_a) esize))))
        let elt2_a ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i sel_a) esize))))
        let elt2_b ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i sel_b) esize))))
        let elt3_r ← (( do (Elem_read operand3 ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let elt3_i ← (( do (Elem_read operand3 ((2 *i p) +i 1) esize) ) : SailM (BitVec esize) )
        let product_r := (elt1_a *i elt2_a)
        let product_i := (elt1_a *i elt2_b)
        let result ← (( do
          if (sub_r : Bool)
          then (do (Elem_set result ((2 *i p) +i 0) esize (BitVec.subInt elt3_r product_r)))
          else (do (Elem_set result ((2 *i p) +i 0) esize (BitVec.addInt elt3_r product_r))) ) : SailM (BitVec VL) )
        if (sub_i : Bool)
        then (do (Elem_set result ((2 *i p) +i 1) esize (BitVec.subInt elt3_i product_i)))
        else (do (Elem_set result ((2 *i p) +i 1) esize (BitVec.addInt elt3_i product_i)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i : Bool, k_sub_r : Bool, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CMLA_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let pairspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (p -i (Nat.mod p pairspersegment))
        let s := (segmentbase +i index)
        let elt1_a ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i p) +i sel_a) esize))))
        let elt2_a ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i sel_a) esize))))
        let elt2_b ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i sel_b) esize))))
        let elt3_r ← (( do (Elem_read operand3 ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let elt3_i ← (( do (Elem_read operand3 ((2 *i p) +i 1) esize) ) : SailM (BitVec esize) )
        let product_r := (elt1_a *i elt2_a)
        let product_i := (elt1_a *i elt2_b)
        let result ← (( do
          if (sub_r : Bool)
          then (do (Elem_set result ((2 *i p) +i 0) esize (BitVec.subInt elt3_r product_r)))
          else (do (Elem_set result ((2 *i p) +i 0) esize (BitVec.addInt elt3_r product_r))) ) : SailM (BitVec VL) )
        if (sub_i : Bool)
        then (do (Elem_set result ((2 *i p) +i 1) esize (BitVec.subInt elt3_i product_i)))
        else (do (Elem_set result ((2 *i p) +i 1) esize (BitVec.addInt elt3_i product_i)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i : Bool, k_sub_r : Bool, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDCMLAH_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let res_i ← (( do (undefined_int ()) ) : SailM Int )
  let res_r ← (( do (undefined_int ()) ) : SailM Int )
  let (res_i, res_r, result) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (res_i, res_r, result)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (res_i, res_r, result) := loop_vars
      loop_vars ← do
        let elt1_a ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i p) +i sel_a) esize))))
        let elt2_a ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i p) +i sel_a) esize))))
        let elt2_b ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i p) +i sel_b) esize))))
        let elt3_r ← (( do (Elem_read operand3 ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let elt3_i ← (( do (Elem_read operand3 ((2 *i p) +i 1) esize) ) : SailM (BitVec esize) )
        let product_r := (elt1_a *i elt2_a)
        let product_i := (elt1_a *i elt2_b)
        let res_r : Int :=
          if (sub_r : Bool)
          then ((Int.shiftl (BitVec.toInt elt3_r) esize) -i (2 *i product_r))
          else ((Int.shiftl (BitVec.toInt elt3_r) esize) +i (2 *i product_r))
        let res_r : Int := (Int.shiftr (res_r +i (Int.shiftl 1 (esize -i 1))) esize)
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (SignedSat res_r esize)))
        let res_i : Int :=
          if (sub_i : Bool)
          then ((Int.shiftl (BitVec.toInt elt3_i) esize) -i (2 *i product_i))
          else ((Int.shiftl (BitVec.toInt elt3_i) esize) +i (2 *i product_i))
        let res_i : Int := (Int.shiftr (res_i +i (Int.shiftl 1 (esize -i 1))) esize)
        let result ← (Elem_set result ((2 *i p) +i 1) esize (← (SignedSat res_i esize)))
        (pure (res_i, res_r, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i : Bool, k_sub_r : Bool, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDCMLAH_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let pairspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let res_i ← (( do (undefined_int ()) ) : SailM Int )
  let res_r ← (( do (undefined_int ()) ) : SailM Int )
  let (res_i, res_r, result) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (res_i, res_r, result)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (res_i, res_r, result) := loop_vars
      loop_vars ← do
        let segmentbase := (p -i (Nat.mod p pairspersegment))
        let s := (segmentbase +i index)
        let elt1_a ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i p) +i sel_a) esize))))
        let elt2_a ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i sel_a) esize))))
        let elt2_b ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i sel_b) esize))))
        let elt3_r ← (( do (Elem_read operand3 ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let elt3_i ← (( do (Elem_read operand3 ((2 *i p) +i 1) esize) ) : SailM (BitVec esize) )
        let product_r := (elt1_a *i elt2_a)
        let product_i := (elt1_a *i elt2_b)
        let res_r : Int :=
          if (sub_r : Bool)
          then ((Int.shiftl (BitVec.toInt elt3_r) esize) -i (2 *i product_r))
          else ((Int.shiftl (BitVec.toInt elt3_r) esize) +i (2 *i product_r))
        let res_r : Int := (Int.shiftr (res_r +i (Int.shiftl 1 (esize -i 1))) esize)
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (SignedSat res_r esize)))
        let res_i : Int :=
          if (sub_i : Bool)
          then ((Int.shiftl (BitVec.toInt elt3_i) esize) -i (2 *i product_i))
          else ((Int.shiftl (BitVec.toInt elt3_i) esize) +i (2 *i product_i))
        let res_i : Int := (Int.shiftr (res_i +i (Int.shiftl 1 (esize -i 1))) esize)
        let result ← (Elem_set result ((2 *i p) +i 1) esize (← (SignedSat res_i esize)))
        (pure (res_i, res_r, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i : Bool, k_sub_r : Bool, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDCMLAH_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let pairspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let res_i ← (( do (undefined_int ()) ) : SailM Int )
  let res_r ← (( do (undefined_int ()) ) : SailM Int )
  let (res_i, res_r, result) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (res_i, res_r, result)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (res_i, res_r, result) := loop_vars
      loop_vars ← do
        let segmentbase := (p -i (Nat.mod p pairspersegment))
        let s := (segmentbase +i index)
        let elt1_a ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i p) +i sel_a) esize))))
        let elt2_a ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i sel_a) esize))))
        let elt2_b ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i sel_b) esize))))
        let elt3_r ← (( do (Elem_read operand3 ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let elt3_i ← (( do (Elem_read operand3 ((2 *i p) +i 1) esize) ) : SailM (BitVec esize) )
        let product_r := (elt1_a *i elt2_a)
        let product_i := (elt1_a *i elt2_b)
        let res_r : Int :=
          if (sub_r : Bool)
          then ((Int.shiftl (BitVec.toInt elt3_r) esize) -i (2 *i product_r))
          else ((Int.shiftl (BitVec.toInt elt3_r) esize) +i (2 *i product_r))
        let res_r : Int := (Int.shiftr (res_r +i (Int.shiftl 1 (esize -i 1))) esize)
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (SignedSat res_r esize)))
        let res_i : Int :=
          if (sub_i : Bool)
          then ((Int.shiftl (BitVec.toInt elt3_i) esize) -i (2 *i product_i))
          else ((Int.shiftl (BitVec.toInt elt3_i) esize) +i (2 *i product_i))
        let res_i : Int := (Int.shiftr (res_i +i (Int.shiftl 1 (esize -i 1))) esize)
        let result ← (Elem_set result ((2 *i p) +i 1) esize (← (SignedSat res_i esize)))
        (pure (res_i, res_r, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MUL_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        let product := (element1 *i element2)
        (Elem_set result e esize (integer_subrange product (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MUL_Z_ZZi_H (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s esize))))
        let res := (element1 *i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MUL_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s esize))))
        let res := (element1 *i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MUL_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s esize))))
        let res := (element1 *i element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_MLA_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s esize))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_MLA_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s esize))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_MLA_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s esize))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_MLS_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s esize))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_MLS_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s esize))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_MLS_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s esize))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        (Elem_set result e esize ((← (Elem_read result e esize)) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMULLB_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := (element1 *i element2)
        (Elem_set result e (2 *i esize) (integer_subrange res ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMULLB_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := (element1 *i element2)
        (Elem_set result e (2 *i esize) (integer_subrange res ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMULLT_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := (element1 *i element2)
        (Elem_set result e (2 *i esize) (integer_subrange res ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMULLT_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := (element1 *i element2)
        (Elem_set result e (2 *i esize) (integer_subrange res ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMULLB_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := (element1 *i element2)
        (Elem_set result e (2 *i esize) (integer_subrange res ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMULLB_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := (element1 *i element2)
        (Elem_set result e (2 *i esize) (integer_subrange res ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMULLT_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := (element1 *i element2)
        (Elem_set result e (2 *i esize) (integer_subrange res ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMULLT_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := (element1 *i element2)
        (Elem_set result e (2 *i esize) (integer_subrange res ((2 *i esize) -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLALB_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLALB_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLALT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLALT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLALB_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLALB_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLALT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLALT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) + product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLSLB_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLSLB_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLSLT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMLSLT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLSLB_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLSLB_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLSLT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMLSLT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) - product))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULLB_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULLB_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULLT_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULLT_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLALB_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e (2 *i esize)))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) (2 *i esize)))))
        let res := (element3 +i product)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLALB_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e (2 *i esize)))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) (2 *i esize)))))
        let res := (element3 +i product)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLALT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e (2 *i esize)))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) (2 *i esize)))))
        let res := (element3 +i product)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLALT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e (2 *i esize)))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) (2 *i esize)))))
        let res := (element3 +i product)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLSLB_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e (2 *i esize)))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) (2 *i esize)))))
        let res := (element3 -i product)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLSLB_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e (2 *i esize)))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) (2 *i esize)))))
        let res := (element3 -i product)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLSLT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e (2 *i esize)))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) (2 *i esize)))))
        let res := (element3 -i product)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, sel = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLSLT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let eltspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let s := (e -i (Nat.mod e eltspersegment))
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel) esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i index) esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e (2 *i esize)))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) (2 *i esize)))))
        let res := (element3 -i product)
        (Elem_set result e (2 *i esize) (← (SignedSat res (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLALBT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2)))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e esize))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) esize))))
        (Elem_set result e esize (← (SignedSat (element3 +i product) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLSLBT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i sel1) (Int.ediv esize 2)))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i sel2) (Int.ediv esize 2)))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read result e esize))))
        let product ← do (pure (BitVec.toInt (← (SignedSat ((2 *i element1) *i element2) esize))))
        (Elem_set result e esize (← (SignedSat (element3 -i product) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMULH_Z_ZZi_H (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMULH_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMULH_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLAH_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let res := ((Int.shiftl element3 esize) +i ((2 *i element1) *i element2))
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLAH_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let res := ((Int.shiftl element3 esize) +i ((2 *i element1) *i element2))
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLAH_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let res := ((Int.shiftl element3 esize) +i ((2 *i element1) *i element2))
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLSH_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let res := ((Int.shiftl element3 esize) -i ((2 *i element1) *i element2))
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLSH_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let res := ((Int.shiftl element3 esize) -i ((2 *i element1) *i element2))
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLSH_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let res := ((Int.shiftl element3 esize) -i ((2 *i element1) *i element2))
        (Elem_set result e esize (← (SignedSat (Int.shiftr (res +i (Int.shiftl 1 (esize -i 1))) esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SHADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (Int.shiftr (element1 +i element2) 1)
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SHSUB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (Int.shiftr (element1 -i element2) 1)
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SHSUBR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (Int.shiftr (element2 -i element1) 1)
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SRHADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (Int.shiftr ((element1 +i element2) +i 1) 1)
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UHADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (Int.shiftr (element1 +i element2) 1)
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UHSUB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (Int.shiftr (element1 -i element2) 1)
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UHSUBR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (Int.shiftr (element2 -i element1) 1)
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_URHADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res := (Int.shiftr ((element1 +i element2) +i 1) 1)
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res ← do (pure (BitVec.toInt (← (Sat (element1 +i element2) esize is_unsigned))))
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res ← do (pure (BitVec.toNat (← (Sat (element1 +i element2) esize is_unsigned))))
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQSUB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res ← do (pure (BitVec.toInt (← (Sat (element1 -i element2) esize is_unsigned))))
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQSUB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res ← do (pure (BitVec.toNat (← (Sat (element1 -i element2) esize is_unsigned))))
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQSUBR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res ← do (pure (BitVec.toInt (← (Sat (element2 -i element1) esize is_unsigned))))
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQSUBR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let res ← do (pure (BitVec.toNat (← (Sat (element2 -i element1) esize is_unsigned))))
            (Elem_set result e esize (integer_subrange res (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SUQADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (SignedSat ((BitVec.toInt element1) +i (BitVec.toNat element2)) esize))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_USQADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (UnsignedSat ((BitVec.toNat element1) +i (BitVec.toInt element2)) esize))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SLI_Z_ZZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read result e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        let mask : (BitVec esize) := ((Ones (n := esize)) <<< shift)
        let shiftedval : (BitVec esize) := (element2 <<< shift)
        (Elem_set result e esize ((element1 &&& (Complement.complement mask)) ||| shiftedval))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SRI_Z_ZZI__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read result e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        let mask : (BitVec esize) := ((Ones (n := esize)) >>> shift)
        let shiftedval : (BitVec esize) := (element2 >>> shift)
        (Elem_set result e esize ((element1 &&& (Complement.complement mask)) ||| shiftedval))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TBX_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        if ((element2 <b elements) : Bool)
        then (do (Elem_set result e esize (← (Elem_read operand1 element2 esize))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_URECPE_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (← (UnsignedRecipEstimate element))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_URSQRTE_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (← (UnsignedRSqrtEstimate element))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_MATCH_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let segmentbase := (e -i (Nat.mod e eltspersegment))
            let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize))
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let loop_i_lower := segmentbase
            let loop_i_upper := ((segmentbase +i eltspersegment) -i 1)
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element2 ← (( do (Elem_read operand2 i esize) ) : SailM (BitVec esize) )
                if ((element1 == element2) : Bool)
                then (do (Elem_set result e psize (Sail.BitVec.zeroExtend 1#1 psize)))
                else (pure result)
            (pure loop_vars_1))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_NMATCH_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let segmentbase := (e -i (Nat.mod e eltspersegment))
            let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend 1#1 psize))
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let loop_i_lower := segmentbase
            let loop_i_upper := ((segmentbase +i eltspersegment) -i 1)
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element2 ← (( do (Elem_read operand2 i esize) ) : SailM (BitVec esize) )
                if ((element1 == element2) : Bool)
                then (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
                else (pure result)
            (pure loop_vars_1))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_HISTCNT_Z_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let count : Int := 0
        let count ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let loop_i_lower := 0
              let loop_i_upper := e
              let mut loop_vars_1 := count
              for i in [loop_i_lower:loop_i_upper:1]i do
                let count := loop_vars_1
                loop_vars_1 ← do
                  if ((← (ActivePredicateElement mask i esize)) : Bool)
                  then
                    (do
                      let element2 ← (( do (Elem_read operand2 i esize) ) : SailM (BitVec esize) )
                      if ((element1 == element2) : Bool)
                      then (pure (count +i 1))
                      else (pure count))
                  else (pure count)
              (pure loop_vars_1))
          else (pure count) ) : SailM Int )
        let count := count
        (Elem_set result e esize (integer_subrange count (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_HISTSEG_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let segments := (Int.ediv VL 128)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_b_lower := 0
    let loop_b_upper := (segments -i 1)
    let mut loop_vars := result
    for b in [loop_b_lower:loop_b_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_s_lower := 0
        let loop_s_upper := (eltspersegment -i 1)
        let mut loop_vars_1 := result
        for s in [loop_s_lower:loop_s_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let count : Int := 0
            let e := ((eltspersegment *i b) +i s)
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let count ← (( do
              let loop_i_lower := 0
              let loop_i_upper := (eltspersegment -i 1)
              let mut loop_vars_2 := count
              for i in [loop_i_lower:loop_i_upper:1]i do
                let count := loop_vars_2
                loop_vars_2 ← do
                  let e2 := ((eltspersegment *i b) +i i)
                  let element2 ← (( do (Elem_read operand2 e2 esize) ) : SailM (BitVec esize) )
                  if ((element1 == element2) : Bool)
                  then (pure (count +i 1))
                  else (pure count)
              (pure loop_vars_2) ) : SailM Int )
            let count := count
            (Elem_set result e esize (integer_subrange count (esize -i 1) 0))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEWR_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec PL) := (Ones (n := PL))
  let src1 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let src2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let operand1 := (BitVec.toNat src1)
  let operand2 := (BitVec.toNat src2)
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let diff := (fdiv_int (operand2 -i operand1) (Int.ediv esize 8))
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if (((diff ≤b 0) || (e <b diff)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend 1#1 psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILERW_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec PL) := (Ones (n := PL))
  let src1 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let src2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let operand1 := (BitVec.toNat src1)
  let operand2 := (BitVec.toNat src2)
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let diff := (Int.ediv (Int.natAbs (operand2 -i operand1)) (Int.ediv esize 8))
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if (((diff == 0) || (e <b diff)) : Bool)
        then (do (Elem_set result e psize (Sail.BitVec.zeroExtend 1#1 psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BDEP_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let data ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let mask ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (← (BitDeposit (← (Elem_read data e esize)) (← (Elem_read mask e esize)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BEXT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let data ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let mask ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (← (BitExtract (← (Elem_read data e esize)) (← (Elem_read mask e esize)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BGRP_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let data ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let mask ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (← (BitGroup (← (Elem_read data e esize)) (← (Elem_read mask e esize)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 1 ∧ sel1 = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_EORBT_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i sel1) esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i sel2) esize) ) : SailM (BitVec esize) )
        (Elem_set result ((2 *i e) +i sel1) esize (element1 ^^^ element2))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2 = 0 ∧ sel1 = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_EORTB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i sel1) esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i sel2) esize) ) : SailM (BitVec esize) )
        (Elem_set result ((2 *i e) +i sel1) esize (element1 ^^^ element2))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i : Bool, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CDOT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let elt1_r ← do (pure (BitVec.toInt (← (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 0) (Int.ediv esize 4)))))
              let elt1_i ← do (pure (BitVec.toInt (← (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 1) (Int.ediv esize 4)))))
              let elt2_a ← do (pure (BitVec.toInt (← (Elem_read operand2 (((4 *i e) +i (2 *i i)) +i sel_a) (Int.ediv esize 4)))))
              let elt2_b ← do (pure (BitVec.toInt (← (Elem_read operand2 (((4 *i e) +i (2 *i i)) +i sel_b) (Int.ediv esize 4)))))
              if (sub_i : Bool)
              then (pure (BitVec.subInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b)))
              else (pure (BitVec.addInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i : Bool, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CDOT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let elt1_r ← do (pure (BitVec.toInt (← (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 0) (Int.ediv esize 4)))))
              let elt1_i ← do (pure (BitVec.toInt (← (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 1) (Int.ediv esize 4)))))
              let elt2_a ← do (pure (BitVec.toInt (← (Elem_read operand2 (((4 *i s) +i (2 *i i)) +i sel_a) (Int.ediv esize 4)))))
              let elt2_b ← do (pure (BitVec.toInt (← (Elem_read operand2 (((4 *i s) +i (2 *i i)) +i sel_b) (Int.ediv esize 4)))))
              if (sub_i : Bool)
              then (pure (BitVec.subInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b)))
              else (pure (BitVec.addInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i : Bool, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CDOT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let res ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let res ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := res
          for i in [loop_i_lower:loop_i_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let elt1_r ← do (pure (BitVec.toInt (← (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 0) (Int.ediv esize 4)))))
              let elt1_i ← do (pure (BitVec.toInt (← (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 1) (Int.ediv esize 4)))))
              let elt2_a ← do (pure (BitVec.toInt (← (Elem_read operand2 (((4 *i s) +i (2 *i i)) +i sel_a) (Int.ediv esize 4)))))
              let elt2_b ← do (pure (BitVec.toInt (← (Elem_read operand2 (((4 *i s) +i (2 *i i)) +i sel_b) (Int.ediv esize 4)))))
              if (sub_i : Bool)
              then (pure (BitVec.subInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b)))
              else (pure (BitVec.addInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b)))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        (Elem_set result e esize res)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let segments := (Int.ediv VL 128)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let op1 ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let op2 ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let addend ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let res ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := (addend, op1, op2, res, result)
    for s in [loop_s_lower:loop_s_upper:1]i do
      let (addend, op1, op2, res, result) := loop_vars
      loop_vars ← do
        let op1 ← (Elem_read operand1 s 128)
        let op2 ← (Elem_read operand2 s 128)
        let addend ← (Elem_read operand3 s 128)
        let res ← (MatMulAdd addend op1 op2 op1_unsigned op2_unsigned)
        let result ← (Elem_set result s 128 res)
        (pure (addend, op1, op2, res, result))
    (pure loop_vars) ) : SailM ((BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let segments := (Int.ediv VL 128)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let op1 ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let op2 ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let addend ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let res ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := (addend, op1, op2, res, result)
    for s in [loop_s_lower:loop_s_upper:1]i do
      let (addend, op1, op2, res, result) := loop_vars
      loop_vars ← do
        let op1 ← (Elem_read operand1 s 128)
        let op2 ← (Elem_read operand2 s 128)
        let addend ← (Elem_read operand3 s 128)
        let res ← (MatMulAdd addend op1 op2 op1_unsigned op2_unsigned)
        let result ← (Elem_set result s 128 res)
        (pure (addend, op1, op2, res, result))
    (pure loop_vars) ) : SailM ((BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_USMMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let segments := (Int.ediv VL 128)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let op1 ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let op2 ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let addend ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let res ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := (addend, op1, op2, res, result)
    for s in [loop_s_lower:loop_s_upper:1]i do
      let (addend, op1, op2, res, result) := loop_vars
      loop_vars ← do
        let op1 ← (Elem_read operand1 s 128)
        let op2 ← (Elem_read operand2 s 128)
        let addend ← (Elem_read operand3 s 128)
        let res ← (MatMulAdd addend op1 op2 op1_unsigned op2_unsigned)
        let result ← (Elem_set result s 128 res)
        (pure (addend, op1, op2, res, result))
    (pure loop_vars) ) : SailM ((BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULH_Z_ZZi_H (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e esize (← (SignedSat (Int.shiftr res esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULH_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e esize (← (SignedSat (Int.shiftr res esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULH_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let eltspersegment := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let segmentbase := (e -i (Nat.mod e eltspersegment))
        let s := (segmentbase +i index)
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s esize))))
        let res := ((2 *i element1) *i element2)
        (Elem_set result e esize (← (SignedSat (Int.shiftr res esize) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SRSRA_Z_ZI__ (VL : Nat) (da : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← do (pure (_shr_int_general ((BitVec.toInt (← (Elem_read operand1 e esize))) +i (_shl_int_general 1 (shift -i 1))) shift))
        (Elem_set result e esize ((← (Elem_read operand2 e esize)) + (integer_subrange element (esize -i 1) 0)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SSRA_Z_ZI__ (VL : Nat) (da : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← do (pure (_shr_int_general (BitVec.toInt (← (Elem_read operand1 e esize))) shift))
        (Elem_set result e esize ((← (Elem_read operand2 e esize)) + (integer_subrange element (esize -i 1) 0)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_URSRA_Z_ZI__ (VL : Nat) (da : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← do (pure (_shr_int_general ((BitVec.toNat (← (Elem_read operand1 e esize))) +i (_shl_int_general 1 (shift -i 1))) shift))
        (Elem_set result e esize ((← (Elem_read operand2 e esize)) + (integer_subrange element (esize -i 1) 0)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_USRA_Z_ZI__ (VL : Nat) (da : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← do (pure (_shr_int_general (BitVec.toNat (← (Elem_read operand1 e esize))) shift))
        (Elem_set result e esize ((← (Elem_read operand2 e esize)) + (integer_subrange element (esize -i 1) 0)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_AESD_Z_ZZ__ (VL : Nat) (dn : Nat) (m : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let segments := (Int.ediv VL 128)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (operand1 ^^^ operand2)
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result s 128 (← (AESInvSubBytes (AESInvShiftRows (← (Elem_read result s 128))))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_AESE_Z_ZZ__ (VL : Nat) (dn : Nat) (m : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let segments := (Int.ediv VL 128)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (operand1 ^^^ operand2)
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result s 128 (← (AESSubBytes (AESShiftRows (← (Elem_read result s 128))))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_AESIMC_Z_Z__ (VL : Nat) (dn : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let segments := (Int.ediv VL 128)
  let operand ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result s 128 (← (AESInvMixColumns (← (Elem_read operand s 128)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_AESMC_Z_Z__ (VL : Nat) (dn : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let segments := (Int.ediv VL 128)
  let operand ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result s 128 (← (AESMixColumns (← (Elem_read operand s 128)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_RAX1_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  if ((← (HaveSME2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 64)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e 64) ) : SailM (BitVec 64) )
        let element2 ← (( do (Elem_read operand2 e 64) ) : SailM (BitVec 64) )
        (Elem_set result e 64 (element1 ^^^ (← (ROL element2 1))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SM4E_Z_ZZ__ (VL : Nat) (dn : Nat) (m : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let segments := (Int.ediv VL 128)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let key ← (( do (Elem_read operand2 s 128) ) : SailM (BitVec 128) )
        let intval ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
        let sboxout ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
        let roundresult ← (( do (Elem_read operand1 s 128) ) : SailM (BitVec 128) )
        let roundkey ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
        let (intval, roundkey, roundresult) ← (( do
          let loop_index_lower := 0
          let loop_index_upper := 3
          let mut loop_vars_1 := (intval, roundkey, roundresult)
          for index in [loop_index_lower:loop_index_upper:1]i do
            let (intval, roundkey, roundresult) := loop_vars_1
            loop_vars_1 ← do
              let roundkey ← (Elem_read key index 32)
              let intval : (BitVec 32) := ((((Sail.BitVec.extractLsb roundresult 127 96) ^^^ (Sail.BitVec.extractLsb roundresult 95 64)) ^^^ (Sail.BitVec.extractLsb roundresult 63 32)) ^^^ roundkey)
              let intval ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := intval
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let intval := loop_vars_2
                  loop_vars_2 ← do (Elem_set intval i 8 (Sbox (← (Elem_read intval i 8))))
                (pure loop_vars_2) ) : SailM (BitVec 32) )
              let intval ← (pure ((((intval ^^^ (← (ROL intval 2))) ^^^ (← (ROL intval 10))) ^^^ (← (ROL intval 18))) ^^^ (← (ROL intval 24))))
              let intval : (BitVec 32) := (intval ^^^ (Sail.BitVec.extractLsb roundresult 31 0))
              let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 31 0 (Sail.BitVec.extractLsb roundresult 63 32))
              let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 63 32 (Sail.BitVec.extractLsb roundresult 95 64))
              let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 95 64 (Sail.BitVec.extractLsb roundresult 127 96))
              let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 127 96 intval)
              (pure (intval, roundkey, roundresult))
          (pure loop_vars_1) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 128)) )
        (Elem_set result s 128 roundresult)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SM4EKEY_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let segments := (Int.ediv VL 128)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let source ← (( do (Elem_read operand2 s 128) ) : SailM (BitVec 128) )
        let intval ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
        let sboxout ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
        let const ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
        let roundresult ← (( do (Elem_read operand1 s 128) ) : SailM (BitVec 128) )
        let (const, intval, roundresult) ← (( do
          let loop_index_lower := 0
          let loop_index_upper := 3
          let mut loop_vars_1 := (const, intval, roundresult)
          for index in [loop_index_lower:loop_index_upper:1]i do
            let (const, intval, roundresult) := loop_vars_1
            loop_vars_1 ← do
              let const ← (Elem_read source index 32)
              let intval : (BitVec 32) := ((((Sail.BitVec.extractLsb roundresult 127 96) ^^^ (Sail.BitVec.extractLsb roundresult 95 64)) ^^^ (Sail.BitVec.extractLsb roundresult 63 32)) ^^^ const)
              let intval ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := intval
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let intval := loop_vars_2
                  loop_vars_2 ← do (Elem_set intval i 8 (Sbox (← (Elem_read intval i 8))))
                (pure loop_vars_2) ) : SailM (BitVec 32) )
              let intval ← (pure ((intval ^^^ (← (ROL intval 13))) ^^^ (← (ROL intval 23))))
              let intval : (BitVec 32) := (intval ^^^ (Sail.BitVec.extractLsb roundresult 31 0))
              let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 31 0 (Sail.BitVec.extractLsb roundresult 63 32))
              let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 63 32 (Sail.BitVec.extractLsb roundresult 95 64))
              let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 95 64 (Sail.BitVec.extractLsb roundresult 127 96))
              let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 127 96 intval)
              (pure (const, intval, roundresult))
          (pure loop_vars_1) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 128)) )
        (Elem_set result s 128 roundresult)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, rot : Int, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_XAR_Z_ZZI__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (rot : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        sail_assert (rot ≥b 0) "src/instrs64_sve.sail:52632.36-52632.37"
        (Elem_set result e esize (ROR (element1 ^^^ element2) rot))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BCAX_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read k VL) ) : SailM (BitVec VL) )
  (Z_set dn VL (operand1 ^^^ (operand2 &&& (Complement.complement operand3))))

/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_EOR3_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read k VL) ) : SailM (BitVec VL) )
  (Z_set dn VL ((operand1 ^^^ operand2) ^^^ operand3))

/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BSL_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read k VL) ) : SailM (BitVec VL) )
  (Z_set dn VL ((operand1 &&& operand3) ||| (operand2 &&& (Complement.complement operand3))))

/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BSL1N_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read k VL) ) : SailM (BitVec VL) )
  (Z_set dn VL (((Complement.complement operand1) &&& operand3) ||| (operand2 &&& (Complement.complement operand3))))

/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BSL2N_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read k VL) ) : SailM (BitVec VL) )
  (Z_set dn VL ((operand1 &&& operand3) ||| ((Complement.complement operand2) &&& (Complement.complement operand3))))

/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_NBSL_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read k VL) ) : SailM (BitVec VL) )
  (Z_set dn VL (Complement.complement ((operand1 &&& operand3) ||| (operand2 &&& (Complement.complement operand3)))))

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_ADCLB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let carry_out ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let res ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let carries ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let (carry_out, nzcv, res, result) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (carry_out, nzcv, res, result)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (carry_out, nzcv, res, result) := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read result ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let carry_in ← (( do (pure (BitVec.join1 [(BitVec.access (← (Elem_read carries ((2 *i p) +i 1) esize)) 0)])) ) : SailM (BitVec 1) )
        let (nzcv, res) : ((BitVec 4) × (BitVec esize)) :=
          let (tup__0, tup__1) := ((AddWithCarry element1 element2 carry_in) : ((BitVec esize) × (BitVec 4)))
          let res : (BitVec esize) := tup__0
          let nzcv : (BitVec 4) := tup__1
          (nzcv, res)
        let carry_out : (BitVec 1) := (BitVec.join1 [(BitVec.access nzcv 1)])
        let result ← (Elem_set result ((2 *i p) +i 0) esize res)
        let result ← (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.zeroExtend carry_out esize))
        (pure (carry_out, nzcv, res, result))
    (pure loop_vars) ) : SailM ((BitVec 1) × (BitVec 4) × (BitVec esize) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_ADCLT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let carry_out ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let res ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let carries ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let (carry_out, nzcv, res, result) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (carry_out, nzcv, res, result)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (carry_out, nzcv, res, result) := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read result ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand ((2 *i p) +i 1) esize) ) : SailM (BitVec esize) )
        let carry_in ← (( do (pure (BitVec.join1 [(BitVec.access (← (Elem_read carries ((2 *i p) +i 1) esize)) 0)])) ) : SailM (BitVec 1) )
        let (nzcv, res) : ((BitVec 4) × (BitVec esize)) :=
          let (tup__0, tup__1) := ((AddWithCarry element1 element2 carry_in) : ((BitVec esize) × (BitVec 4)))
          let res : (BitVec esize) := tup__0
          let nzcv : (BitVec 4) := tup__1
          (nzcv, res)
        let carry_out : (BitVec 1) := (BitVec.join1 [(BitVec.access nzcv 1)])
        let result ← (Elem_set result ((2 *i p) +i 0) esize res)
        let result ← (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.zeroExtend carry_out esize))
        (pure (carry_out, nzcv, res, result))
    (pure loop_vars) ) : SailM ((BitVec 1) × (BitVec 4) × (BitVec esize) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SBCLB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let carry_out ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let res ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let carries ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let (carry_out, nzcv, res, result) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (carry_out, nzcv, res, result)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (carry_out, nzcv, res, result) := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read result ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let carry_in ← (( do (pure (BitVec.join1 [(BitVec.access (← (Elem_read carries ((2 *i p) +i 1) esize)) 0)])) ) : SailM (BitVec 1) )
        let (nzcv, res) : ((BitVec 4) × (BitVec esize)) :=
          let (tup__0, tup__1) := ((AddWithCarry element1 (Complement.complement element2) carry_in) : ((BitVec esize) × (BitVec 4)))
          let res : (BitVec esize) := tup__0
          let nzcv : (BitVec 4) := tup__1
          (nzcv, res)
        let carry_out : (BitVec 1) := (BitVec.join1 [(BitVec.access nzcv 1)])
        let result ← (Elem_set result ((2 *i p) +i 0) esize res)
        let result ← (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.zeroExtend carry_out esize))
        (pure (carry_out, nzcv, res, result))
    (pure loop_vars) ) : SailM ((BitVec 1) × (BitVec 4) × (BitVec esize) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SBCLT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let carry_out ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let res ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let carries ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let (carry_out, nzcv, res, result) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (carry_out, nzcv, res, result)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (carry_out, nzcv, res, result) := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read result ((2 *i p) +i 0) esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand ((2 *i p) +i 1) esize) ) : SailM (BitVec esize) )
        let carry_in ← (( do (pure (BitVec.join1 [(BitVec.access (← (Elem_read carries ((2 *i p) +i 1) esize)) 0)])) ) : SailM (BitVec 1) )
        let (nzcv, res) : ((BitVec 4) × (BitVec esize)) :=
          let (tup__0, tup__1) := ((AddWithCarry element1 (Complement.complement element2) carry_in) : ((BitVec esize) × (BitVec 4)))
          let res : (BitVec esize) := tup__0
          let nzcv : (BitVec 4) := tup__1
          (nzcv, res)
        let carry_out : (BitVec 1) := (BitVec.join1 [(BitVec.access nzcv 1)])
        let result ← (Elem_set result ((2 *i p) +i 0) esize res)
        let result ← (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.zeroExtend carry_out esize))
        (pure (carry_out, nzcv, res, result))
    (pure loop_vars) ) : SailM ((BitVec 1) × (BitVec 4) × (BitVec esize) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMULH_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let product := (Int.shiftr (element1 *i element2) esize)
        (Elem_set result e esize (integer_subrange product (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMULH_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let product := (Int.shiftr (element1 *i element2) esize)
        (Elem_set result e esize (integer_subrange product (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCLAMP_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let res := (Min.min (Max.max element1 element3) element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCLAMP_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
        let element3 ← do (pure (BitVec.toNat (← (Elem_read operand3 e esize))))
        let res := (Min.min (Max.max element1 element3) element2)
        (Elem_set result e esize (integer_subrange res (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, swsize : Nat, swsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_REVD_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (swsize : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize (← (Reverse element swsize))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, m : Nat, n : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ imm ∧ imm ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PSEL_P_PPi__ (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (m : Nat) (n : Nat) (v : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let idx ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let element := (Nat.mod ((BitVec.toNat idx) +i imm) elements)
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let result ← (( do
    if ((← (ActivePredicateElement operand2 element esize)) : Bool)
    then (pure operand1)
    else (pure (Zeros (n := PL))) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELO_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec (PL * 2)) := (Ones (n := (PL *i 2)))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector (PL *i 2)) ) : SailM (BitVec (PL * 2)) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((elements *i 2) -i 1)
    let mut loop_vars := (last, operand1, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (last, operand1, result) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_LT => (do (pure ((← (asl_Int operand1 is_unsigned)) <b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_LE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≤b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let pbit : (BitVec 1) :=
          if (last : Bool)
          then 1#1
          else 0#1
        let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
        let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
        (pure (last, operand1, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec (PL * 2))) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL (Sail.BitVec.extractLsb result (PL -i 1) 0))
  (P_set d1 PL (Sail.BitVec.extractLsb result ((PL *i 2) -i 1) PL))

/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELS_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec (PL * 2)) := (Ones (n := (PL *i 2)))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector (PL *i 2)) ) : SailM (BitVec (PL * 2)) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((elements *i 2) -i 1)
    let mut loop_vars := (last, operand1, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (last, operand1, result) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_LT => (do (pure ((← (asl_Int operand1 is_unsigned)) <b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_LE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≤b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let pbit : (BitVec 1) :=
          if (last : Bool)
          then 1#1
          else 0#1
        let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
        let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
        (pure (last, operand1, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec (PL * 2))) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL (Sail.BitVec.extractLsb result (PL -i 1) 0))
  (P_set d1 PL (Sail.BitVec.extractLsb result ((PL *i 2) -i 1) PL))

/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELT_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec (PL * 2)) := (Ones (n := (PL *i 2)))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector (PL *i 2)) ) : SailM (BitVec (PL * 2)) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((elements *i 2) -i 1)
    let mut loop_vars := (last, operand1, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (last, operand1, result) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_LT => (do (pure ((← (asl_Int operand1 is_unsigned)) <b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_LE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≤b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let pbit : (BitVec 1) :=
          if (last : Bool)
          then 1#1
          else 0#1
        let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
        let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
        (pure (last, operand1, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec (PL * 2))) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL (Sail.BitVec.extractLsb result (PL -i 1) 0))
  (P_set d1 PL (Sail.BitVec.extractLsb result ((PL *i 2) -i 1) PL))

/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELE_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec (PL * 2)) := (Ones (n := (PL *i 2)))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector (PL *i 2)) ) : SailM (BitVec (PL * 2)) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((elements *i 2) -i 1)
    let mut loop_vars := (last, operand1, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (last, operand1, result) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_LT => (do (pure ((← (asl_Int operand1 is_unsigned)) <b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_LE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≤b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let pbit : (BitVec 1) :=
          if (last : Bool)
          then 1#1
          else 0#1
        let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
        let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
        (pure (last, operand1, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec (PL * 2))) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL (Sail.BitVec.extractLsb result (PL -i 1) 0))
  (P_set d1 PL (Sail.BitVec.extractLsb result ((PL *i 2) -i 1) PL))

/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHI_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec (PL * 2)) := (Ones (n := (PL *i 2)))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector (PL *i 2)) ) : SailM (BitVec (PL * 2)) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((elements *i 2) -i 1)
    let mut loop_vars := (last, operand1, result)
    for e in [loop_e_upper:loop_e_lower:-1]i do
      let (last, operand1, result) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_GT => (do (pure ((← (asl_Int operand1 is_unsigned)) >b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_GE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≥b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let pbit : (BitVec 1) :=
          if (last : Bool)
          then 1#1
          else 0#1
        let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
        let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
        (pure (last, operand1, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec (PL * 2))) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL (Sail.BitVec.extractLsb result (PL -i 1) 0))
  (P_set d1 PL (Sail.BitVec.extractLsb result ((PL *i 2) -i 1) PL))

/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHS_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec (PL * 2)) := (Ones (n := (PL *i 2)))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector (PL *i 2)) ) : SailM (BitVec (PL * 2)) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((elements *i 2) -i 1)
    let mut loop_vars := (last, operand1, result)
    for e in [loop_e_upper:loop_e_lower:-1]i do
      let (last, operand1, result) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_GT => (do (pure ((← (asl_Int operand1 is_unsigned)) >b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_GE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≥b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let pbit : (BitVec 1) :=
          if (last : Bool)
          then 1#1
          else 0#1
        let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
        let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
        (pure (last, operand1, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec (PL * 2))) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL (Sail.BitVec.extractLsb result (PL -i 1) 0))
  (P_set d1 PL (Sail.BitVec.extractLsb result ((PL *i 2) -i 1) PL))

/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGT_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec (PL * 2)) := (Ones (n := (PL *i 2)))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector (PL *i 2)) ) : SailM (BitVec (PL * 2)) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((elements *i 2) -i 1)
    let mut loop_vars := (last, operand1, result)
    for e in [loop_e_upper:loop_e_lower:-1]i do
      let (last, operand1, result) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_GT => (do (pure ((← (asl_Int operand1 is_unsigned)) >b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_GE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≥b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let pbit : (BitVec 1) :=
          if (last : Bool)
          then 1#1
          else 0#1
        let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
        let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
        (pure (last, operand1, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec (PL * 2))) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL (Sail.BitVec.extractLsb result (PL -i 1) 0))
  (P_set d1 PL (Sail.BitVec.extractLsb result ((PL *i 2) -i 1) PL))

/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGE_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec (PL * 2)) := (Ones (n := (PL *i 2)))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector (PL *i 2)) ) : SailM (BitVec (PL * 2)) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((elements *i 2) -i 1)
    let mut loop_vars := (last, operand1, result)
    for e in [loop_e_upper:loop_e_lower:-1]i do
      let (last, operand1, result) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_GT => (do (pure ((← (asl_Int operand1 is_unsigned)) >b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_GE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≥b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let pbit : (BitVec 1) :=
          if (last : Bool)
          then 1#1
          else 0#1
        let result ← (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
        let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
        (pure (last, operand1, result))
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec (PL * 2))) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL (Sail.BitVec.extractLsb result (PL -i 1) 0))
  (P_set d1 PL (Sail.BitVec.extractLsb result ((PL *i 2) -i 1) PL))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 1
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
            let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((2 *i e) +i i) esize (← (SignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRUN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 1
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
            let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((2 *i e) +i i) esize (← (UnsignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHRN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 1
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
            let res := (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((2 *i e) +i i) esize (← (UnsignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 1
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← do (pure (BitVec.toInt (← (Elem_read operand e (2 *i esize)))))
            (Elem_set result ((2 *i e) +i i) esize (← (SignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTUN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 1
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← do (pure (BitVec.toInt (← (Elem_read operand e (2 *i esize)))))
            (Elem_set result ((2 *i e) +i i) esize (← (UnsignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQCVTN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 1
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← do (pure (BitVec.toNat (← (Elem_read operand e (2 *i esize)))))
            (Elem_set result ((2 *i e) +i i) esize (← (UnsignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_DUPQ_Z_Zi__ (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elements := (Int.ediv 128 esize)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := (element, result)
    for s in [loop_s_lower:loop_s_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand ((s *i elements) +i index) esize)
        let result ← (Elem_set result s 128 (BitVec.replicateBits element (Int.ediv 128 esize)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec VL)) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, position : Int, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_EXTQ_Z_ZI_Des (VL : Nat) (dn : Nat) (m : Nat) (position : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let concat ← (( do (pure ((← (Elem_read operand2 s 128)) +++ (← (Elem_read operand1 s 128)))) ) : SailM (BitVec 256) )
        sail_assert ((0 ≤b position) && ((position +i 127) <b 256)) "src/instrs64_sve.sail:54880.67-54880.68"
        (Elem_set result s 128 (Sail.BitVec.extractLsb concat (position +i 127) position))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TBLQ_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elements := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let idx ← do (pure (BitVec.toNat (← (Elem_read operand2 ((s *i elements) +i e) esize))))
            if ((idx <b elements) : Bool)
            then (do (Elem_set result ((s *i elements) +i e) esize (← (Elem_read operand1 ((s *i elements) +i idx) esize))))
            else (do (Elem_set result ((s *i elements) +i e) esize (Zeros (n := esize))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TBXQ_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elements := (Int.ediv 128 esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let idx ← do (pure (BitVec.toNat (← (Elem_read operand2 ((s *i elements) +i e) esize))))
            if ((idx <b elements) : Bool)
            then (do (Elem_set result ((s *i elements) +i e) esize (← (Elem_read operand1 ((s *i elements) +i idx) esize))))
            else (pure result)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZPQ1_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elements := (Int.ediv 128 esize)
  let pairs := (Int.ediv elements 2)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (( do
          let loop_p_lower := 0
          let loop_p_upper := (pairs -i 1)
          let mut loop_vars_1 := result
          for p in [loop_p_lower:loop_p_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do (Elem_set result ((s *i elements) +i p) esize (← (Elem_read operand1 (((s *i elements) +i (2 *i p)) +i part) esize)))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let loop_p_lower := 0
        let loop_p_upper := (pairs -i 1)
        let mut loop_vars_2 := result
        for p in [loop_p_lower:loop_p_upper:1]i do
          let result := loop_vars_2
          loop_vars_2 ← do (Elem_set result (((s *i elements) +i pairs) +i p) esize (← (Elem_read operand2 (((s *i elements) +i (2 *i p)) +i part) esize)))
        (pure loop_vars_2)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZPQ2_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elements := (Int.ediv 128 esize)
  let pairs := (Int.ediv elements 2)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (( do
          let loop_p_lower := 0
          let loop_p_upper := (pairs -i 1)
          let mut loop_vars_1 := result
          for p in [loop_p_lower:loop_p_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do (Elem_set result ((s *i elements) +i p) esize (← (Elem_read operand1 (((s *i elements) +i (2 *i p)) +i part) esize)))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let loop_p_lower := 0
        let loop_p_upper := (pairs -i 1)
        let mut loop_vars_2 := result
        for p in [loop_p_lower:loop_p_upper:1]i do
          let result := loop_vars_2
          loop_vars_2 ← do (Elem_set result (((s *i elements) +i pairs) +i p) esize (← (Elem_read operand2 (((s *i elements) +i (2 *i p)) +i part) esize)))
        (pure loop_vars_2)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIPQ1_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elements := (Int.ediv 128 esize)
  let pairs := (Int.ediv elements 2)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let base := ((s *i elements) +i (part *i pairs))
        let loop_p_lower := 0
        let loop_p_upper := (pairs -i 1)
        let mut loop_vars_1 := result
        for p in [loop_p_lower:loop_p_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let result ← (Elem_set result (((s *i elements) +i (2 *i p)) +i 0) esize (← (Elem_read operand1 (base +i p) esize)))
            (Elem_set result (((s *i elements) +i (2 *i p)) +i 1) esize (← (Elem_read operand2 (base +i p) esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIPQ2_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elements := (Int.ediv 128 esize)
  let pairs := (Int.ediv elements 2)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let base := ((s *i elements) +i (part *i pairs))
        let loop_p_lower := 0
        let loop_p_upper := (pairs -i 1)
        let mut loop_vars_1 := result
        for p in [loop_p_lower:loop_p_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let result ← (Elem_set result (((s *i elements) +i (2 *i p)) +i 0) esize (← (Elem_read operand1 (base +i p) esize)))
            (Elem_set result (((s *i elements) +i (2 *i p)) +i 1) esize (← (Elem_read operand2 (base +i p) esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ANDQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elempersegment := (Int.ediv 128 esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := (dtmp, result, stmp)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (dtmp, result, stmp) := loop_vars
      loop_vars ← do
        let dtmp : (BitVec esize) := (Ones (n := esize))
        let (dtmp, stmp) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (segments -i 1)
          let mut loop_vars_1 := (dtmp, stmp)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (dtmp, stmp) := loop_vars_1
            loop_vars_1 ← do
              let (dtmp, stmp) ← (( do
                if ((← (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)) : Bool)
                then
                  (do
                    let stmp ← (Elem_read operand s 128)
                    let dtmp ← (pure (dtmp &&& (← (Elem_read stmp e esize))))
                    (pure (dtmp, stmp)))
                else (pure (dtmp, stmp)) ) : SailM ((BitVec esize) × (BitVec 128)) )
              (pure (dtmp, stmp))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec 128)) )
        let result ← (Elem_set result e esize (Sail.BitVec.extractLsb dtmp (esize -i 1) 0))
        (pure (dtmp, result, stmp))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_EORQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elempersegment := (Int.ediv 128 esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := (dtmp, result, stmp)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (dtmp, result, stmp) := loop_vars
      loop_vars ← do
        let dtmp : (BitVec esize) := (Zeros (n := esize))
        let (dtmp, stmp) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (segments -i 1)
          let mut loop_vars_1 := (dtmp, stmp)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (dtmp, stmp) := loop_vars_1
            loop_vars_1 ← do
              let (dtmp, stmp) ← (( do
                if ((← (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)) : Bool)
                then
                  (do
                    let stmp ← (Elem_read operand s 128)
                    let dtmp ← (pure (dtmp ^^^ (← (Elem_read stmp e esize))))
                    (pure (dtmp, stmp)))
                else (pure (dtmp, stmp)) ) : SailM ((BitVec esize) × (BitVec 128)) )
              (pure (dtmp, stmp))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec 128)) )
        let result ← (Elem_set result e esize (Sail.BitVec.extractLsb dtmp (esize -i 1) 0))
        (pure (dtmp, result, stmp))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ORQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elempersegment := (Int.ediv 128 esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := (dtmp, result, stmp)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (dtmp, result, stmp) := loop_vars
      loop_vars ← do
        let dtmp : (BitVec esize) := (Zeros (n := esize))
        let (dtmp, stmp) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (segments -i 1)
          let mut loop_vars_1 := (dtmp, stmp)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (dtmp, stmp) := loop_vars_1
            loop_vars_1 ← do
              let (dtmp, stmp) ← (( do
                if ((← (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)) : Bool)
                then
                  (do
                    let stmp ← (Elem_read operand s 128)
                    let dtmp ← (pure (dtmp ||| (← (Elem_read stmp e esize))))
                    (pure (dtmp, stmp)))
                else (pure (dtmp, stmp)) ) : SailM ((BitVec esize) × (BitVec 128)) )
              (pure (dtmp, stmp))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec 128)) )
        let result ← (Elem_set result e esize (Sail.BitVec.extractLsb dtmp (esize -i 1) 0))
        (pure (dtmp, result, stmp))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADDQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elempersegment := (Int.ediv 128 esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_int ()) ) : SailM Int )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := (dtmp, result, stmp)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (dtmp, result, stmp) := loop_vars
      loop_vars ← do
        let dtmp : Int := 0
        let (dtmp, stmp) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (segments -i 1)
          let mut loop_vars_1 := (dtmp, stmp)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (dtmp, stmp) := loop_vars_1
            loop_vars_1 ← do
              let (dtmp, stmp) ← (( do
                if ((← (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)) : Bool)
                then
                  (do
                    let stmp ← (Elem_read operand s 128)
                    let dtmp ← (pure (dtmp +i (BitVec.toNat (← (Elem_read stmp e esize)))))
                    (pure (dtmp, stmp)))
                else (pure (dtmp, stmp)) ) : SailM (Int × (BitVec 128)) )
              (pure (dtmp, stmp))
          (pure loop_vars_1) ) : SailM (Int × (BitVec 128)) )
        let result ← (Elem_set result e esize (integer_subrange dtmp (esize -i 1) 0))
        (pure (dtmp, result, stmp))
    (pure loop_vars) ) : SailM (Int × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMAXQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elempersegment := (Int.ediv 128 esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_int ()) ) : SailM Int )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := (dtmp, result, stmp)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (dtmp, result, stmp) := loop_vars
      loop_vars ← do
        let dtmp : Int :=
          if (is_unsigned : Bool)
          then 0
          else (Neg.neg (2 ^i (esize -i 1)))
        let (dtmp, stmp) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (segments -i 1)
          let mut loop_vars_1 := (dtmp, stmp)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (dtmp, stmp) := loop_vars_1
            loop_vars_1 ← do
              let (dtmp, stmp) ← (( do
                if ((← (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)) : Bool)
                then
                  (do
                    let stmp ← (Elem_read operand s 128)
                    let dtmp ← (pure (Max.max dtmp (BitVec.toInt (← (Elem_read stmp e esize)))))
                    (pure (dtmp, stmp)))
                else (pure (dtmp, stmp)) ) : SailM (Int × (BitVec 128)) )
              (pure (dtmp, stmp))
          (pure loop_vars_1) ) : SailM (Int × (BitVec 128)) )
        let result ← (Elem_set result e esize (integer_subrange dtmp (esize -i 1) 0))
        (pure (dtmp, result, stmp))
    (pure loop_vars) ) : SailM (Int × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMAXQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elempersegment := (Int.ediv 128 esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_int ()) ) : SailM Int )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := (dtmp, result, stmp)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (dtmp, result, stmp) := loop_vars
      loop_vars ← do
        let dtmp : Int :=
          if (is_unsigned : Bool)
          then 0
          else (Neg.neg (2 ^i (esize -i 1)))
        let (dtmp, stmp) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (segments -i 1)
          let mut loop_vars_1 := (dtmp, stmp)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (dtmp, stmp) := loop_vars_1
            loop_vars_1 ← do
              let (dtmp, stmp) ← (( do
                if ((← (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)) : Bool)
                then
                  (do
                    let stmp ← (Elem_read operand s 128)
                    let dtmp ← (pure (Max.max dtmp (BitVec.toNat (← (Elem_read stmp e esize)))))
                    (pure (dtmp, stmp)))
                else (pure (dtmp, stmp)) ) : SailM (Int × (BitVec 128)) )
              (pure (dtmp, stmp))
          (pure loop_vars_1) ) : SailM (Int × (BitVec 128)) )
        let result ← (Elem_set result e esize (integer_subrange dtmp (esize -i 1) 0))
        (pure (dtmp, result, stmp))
    (pure loop_vars) ) : SailM (Int × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMINQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elempersegment := (Int.ediv 128 esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_int ()) ) : SailM Int )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := (dtmp, result, stmp)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (dtmp, result, stmp) := loop_vars
      loop_vars ← do
        let dtmp : Int :=
          if (is_unsigned : Bool)
          then ((2 ^i esize) -i 1)
          else ((2 ^i (esize -i 1)) -i 1)
        let (dtmp, stmp) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (segments -i 1)
          let mut loop_vars_1 := (dtmp, stmp)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (dtmp, stmp) := loop_vars_1
            loop_vars_1 ← do
              let (dtmp, stmp) ← (( do
                if ((← (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)) : Bool)
                then
                  (do
                    let stmp ← (Elem_read operand s 128)
                    let dtmp ← (pure (Min.min dtmp (BitVec.toInt (← (Elem_read stmp e esize)))))
                    (pure (dtmp, stmp)))
                else (pure (dtmp, stmp)) ) : SailM (Int × (BitVec 128)) )
              (pure (dtmp, stmp))
          (pure loop_vars_1) ) : SailM (Int × (BitVec 128)) )
        let result ← (Elem_set result e esize (integer_subrange dtmp (esize -i 1) 0))
        (pure (dtmp, result, stmp))
    (pure loop_vars) ) : SailM (Int × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMINQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let elempersegment := (Int.ediv 128 esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_int ()) ) : SailM Int )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := (dtmp, result, stmp)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (dtmp, result, stmp) := loop_vars
      loop_vars ← do
        let dtmp : Int :=
          if (is_unsigned : Bool)
          then ((2 ^i esize) -i 1)
          else ((2 ^i (esize -i 1)) -i 1)
        let (dtmp, stmp) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (segments -i 1)
          let mut loop_vars_1 := (dtmp, stmp)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (dtmp, stmp) := loop_vars_1
            loop_vars_1 ← do
              let (dtmp, stmp) ← (( do
                if ((← (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)) : Bool)
                then
                  (do
                    let stmp ← (Elem_read operand s 128)
                    let dtmp ← (pure (Min.min dtmp (BitVec.toNat (← (Elem_read stmp e esize)))))
                    (pure (dtmp, stmp)))
                else (pure (dtmp, stmp)) ) : SailM (Int × (BitVec 128)) )
              (pure (dtmp, stmp))
          (pure loop_vars_1) ) : SailM (Int × (BitVec 128)) )
        let result ← (Elem_set result e esize (integer_subrange dtmp (esize -i 1) 0))
        (pure (dtmp, result, stmp))
    (pure loop_vars) ) : SailM (Int × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ imm = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMOV_Z_PI_B (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (pure (BitVec.update result ((elements *i imm) +i e) (Bit (← (PredicateElement operand e esize)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ List.elem imm [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMOV_Z_PI_H (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    if ((imm == 0) : Bool)
    then (pure (Zeros (n := VL)))
    else (do (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (pure (BitVec.update result ((elements *i imm) +i e) (Bit (← (PredicateElement operand e esize)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ List.elem imm [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMOV_Z_PI_S (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    if ((imm == 0) : Bool)
    then (pure (Zeros (n := VL)))
    else (do (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (pure (BitVec.update result ((elements *i imm) +i e) (Bit (← (PredicateElement operand e esize)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMOV_Z_PI_D (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    if ((imm == 0) : Bool)
    then (pure (Zeros (n := VL)))
    else (do (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (pure (BitVec.update result ((elements *i imm) +i e) (Bit (← (PredicateElement operand e esize)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ imm = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PMOV_P_ZI_B (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e psize (Sail.BitVec.zeroExtend (BitVec.join1 [(BitVec.access operand ((elements *i imm) +i e))]) psize))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem imm [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PMOV_P_ZI_H (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e psize (Sail.BitVec.zeroExtend (BitVec.join1 [(BitVec.access operand ((elements *i imm) +i e))]) psize))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem imm [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PMOV_P_ZI_S (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e psize (Sail.BitVec.zeroExtend (BitVec.join1 [(BitVec.access operand ((elements *i imm) +i e))]) psize))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PMOV_P_ZI_D (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e psize (Sail.BitVec.zeroExtend (BitVec.join1 [(BitVec.access operand ((elements *i imm) +i e))]) psize))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, part : Nat, List.elem part [0, 1, 2, 3] ∧ 0 ≤ n ∧ n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PEXT_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let pred ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i 4)) ) : SailM (BitVec (PL * 4)) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let pbit ← (( do (PredicateElement mask ((part *i elements) +i e) esize) ) : SailM (BitVec 1) )
        (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Int, esize : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_PEXT_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Int) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let pred ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i 4)) ) : SailM (BitVec (PL * 4)) )
  let result0 ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let result1 ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result0 ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result0
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result0 := loop_vars
      loop_vars ← do
        let pbit ← (( do (PredicateElement mask (((part *i 2) *i elements) +i e) esize) ) : SailM (BitVec 1) )
        (Elem_set result0 e psize (Sail.BitVec.zeroExtend pbit psize))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let result1 ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars_1 := result1
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result1 := loop_vars_1
      loop_vars_1 ← do
        let pbit ← (( do (PredicateElement mask ((((part *i 2) *i elements) +i elements) +i e) esize) ) : SailM (BitVec 1) )
        (Elem_set result1 e psize (Sail.BitVec.zeroExtend pbit psize))
    (pure loop_vars_1) ) : SailM (BitVec PL) )
  (P_set d0 PL result0)
  (P_set d1 PL result1)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PTRUE_PN_I__ (VL : Nat) (d : Nat) (esize : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let result ← (( do (EncodePredCount esize elements elements false PL) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, width : Nat, List.elem width [2, 4] ∧ 0 ≤ n ∧ n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CNTP_R_PN__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (width : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let pred ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i 4)) ) : SailM (BitVec (PL * 4)) )
  let sum : (BitVec 64) := (Zeros (n := 64))
  let limit := (elements *i width)
  let sum ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (limit -i 1)
    let mut loop_vars := sum
    for e in [loop_e_lower:loop_e_upper:1]i do
      let sum := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (pure (BitVec.addInt sum 1))
        else (pure sum)
    (pure loop_vars) ) : SailM (BitVec 64) )
  (X_set d 64 sum)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧ rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELO_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (width *i (Int.ediv VL esize))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, last, operand1)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (count, last, operand1) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_LT => (do (pure ((← (asl_Int operand1 is_unsigned)) <b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_LE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≤b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let count : Int :=
          if (last : Bool)
          then (count +i 1)
          else count
        let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
        (pure (count, last, operand1))
    (pure loop_vars) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count := count
  let result ← (( do (EncodePredCount esize elements count invert PL) ) : SailM (BitVec PL) )
  let split_vec ← do (PredCountTest elements count invert)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧ rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELS_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (width *i (Int.ediv VL esize))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, last, operand1)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (count, last, operand1) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_LT => (do (pure ((← (asl_Int operand1 is_unsigned)) <b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_LE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≤b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let count : Int :=
          if (last : Bool)
          then (count +i 1)
          else count
        let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
        (pure (count, last, operand1))
    (pure loop_vars) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count := count
  let result ← (( do (EncodePredCount esize elements count invert PL) ) : SailM (BitVec PL) )
  let split_vec ← do (PredCountTest elements count invert)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧ rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELT_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (width *i (Int.ediv VL esize))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, last, operand1)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (count, last, operand1) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_LT => (do (pure ((← (asl_Int operand1 is_unsigned)) <b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_LE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≤b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let count : Int :=
          if (last : Bool)
          then (count +i 1)
          else count
        let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
        (pure (count, last, operand1))
    (pure loop_vars) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count := count
  let result ← (( do (EncodePredCount esize elements count invert PL) ) : SailM (BitVec PL) )
  let split_vec ← do (PredCountTest elements count invert)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧ rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELE_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (width *i (Int.ediv VL esize))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, last, operand1)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (count, last, operand1) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_LT => (do (pure ((← (asl_Int operand1 is_unsigned)) <b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_LE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≤b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let count : Int :=
          if (last : Bool)
          then (count +i 1)
          else count
        let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
        (pure (count, last, operand1))
    (pure loop_vars) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count := count
  let result ← (( do (EncodePredCount esize elements count invert PL) ) : SailM (BitVec PL) )
  let split_vec ← do (PredCountTest elements count invert)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧ rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHI_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (width *i (Int.ediv VL esize))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, last, operand1)
    for e in [loop_e_upper:loop_e_lower:-1]i do
      let (count, last, operand1) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_GT => (do (pure ((← (asl_Int operand1 is_unsigned)) >b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_GE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≥b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let count : Int :=
          if (last : Bool)
          then (count +i 1)
          else count
        let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
        (pure (count, last, operand1))
    (pure loop_vars) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count := count
  let result ← (( do (EncodePredCount esize elements count invert PL) ) : SailM (BitVec PL) )
  let split_vec ← do (PredCountTest elements count invert)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧ rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHS_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (width *i (Int.ediv VL esize))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, last, operand1)
    for e in [loop_e_upper:loop_e_lower:-1]i do
      let (count, last, operand1) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_GT => (do (pure ((← (asl_Int operand1 is_unsigned)) >b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_GE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≥b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let count : Int :=
          if (last : Bool)
          then (count +i 1)
          else count
        let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
        (pure (count, last, operand1))
    (pure loop_vars) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count := count
  let result ← (( do (EncodePredCount esize elements count invert PL) ) : SailM (BitVec PL) )
  let split_vec ← do (PredCountTest elements count invert)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧ rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGT_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (width *i (Int.ediv VL esize))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, last, operand1)
    for e in [loop_e_upper:loop_e_lower:-1]i do
      let (count, last, operand1) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_GT => (do (pure ((← (asl_Int operand1 is_unsigned)) >b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_GE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≥b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let count : Int :=
          if (last : Bool)
          then (count +i 1)
          else count
        let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
        (pure (count, last, operand1))
    (pure loop_vars) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count := count
  let result ← (( do (EncodePredCount esize elements count invert PL) ) : SailM (BitVec PL) )
  let split_vec ← do (PredCountTest elements count invert)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧ rsize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGE_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (width *i (Int.ediv VL esize))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, last, operand1)
    for e in [loop_e_upper:loop_e_lower:-1]i do
      let (count, last, operand1) := loop_vars
      loop_vars ← do
        let cond ← (( do (undefined_bool ()) ) : SailM Bool )
        let cond ← (( do
          match op with
          | .Cmp_GT => (do (pure ((← (asl_Int operand1 is_unsigned)) >b (← (asl_Int operand2 is_unsigned)))))
          | .Cmp_GE => (do (pure ((← (asl_Int operand1 is_unsigned)) ≥b (← (asl_Int operand2 is_unsigned)))))
          | _ => (pure cond) ) : SailM Bool )
        let last : Bool := (last && cond)
        let count : Int :=
          if (last : Bool)
          then (count +i 1)
          else count
        let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
        (pure (count, last, operand1))
    (pure loop_vars) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count := count
  let result ← (( do (EncodePredCount esize elements count invert PL) ) : SailM (BitVec PL) )
  let split_vec ← do (PredCountTest elements count invert)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let (data, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, result) := loop_vars
      loop_vars ← do
        let (data, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let data ← (Mem_read addr mbytes accdesc)
              let result ← (Elem_set result e esize (← (Extend data esize is_unsigned)))
              (pure (data, result)))
          else
            (do
              let result ← (Elem_set result e esize (Zeros (n := esize)))
              (pure (data, result))) ) : SailM ((BitVec msize) × (BitVec VL)) )
        (pure (data, result))
    (pure loop_vars) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let (data, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, result) := loop_vars
      loop_vars ← do
        let (data, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let data ← (Mem_read addr mbytes accdesc)
              let result ← (Elem_set result e esize (← (Extend data esize is_unsigned)))
              (pure (data, result)))
          else
            (do
              let result ← (Elem_set result e esize (Zeros (n := esize)))
              (pure (data, result))) ) : SailM ((BitVec msize) × (BitVec VL)) )
        (pure (data, result))
    (pure loop_vars) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1B_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVEFF contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:57610.24-57610.25"
  let (accdesc, data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (accdesc, data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (accdesc, data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (accdesc, data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let (accdesc, data, fault) ← (( do
                if (accdesc.first : Bool)
                then
                  (do
                    let data ← (Mem_read addr mbytes accdesc)
                    let accdesc : AccessDescriptor := { accdesc with first := false }
                    (pure (accdesc, data, fault)))
                else
                  (do
                    let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
                    let data : (BitVec msize) := tup__0
                    let fault : Bool := tup__1
                    (pure (accdesc, data, fault))) ) : SailM (AccessDescriptor × (BitVec msize) × Bool) )
              (pure (accdesc, data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (accdesc, data, fault))) ) : SailM (AccessDescriptor × (BitVec msize) × Bool) )
        let faulted : Bool := (faulted || fault)
        if (faulted : Bool)
        then (ElemFFR_set e esize 0#1)
        else (pure ())
        let unknown ← (pure unknown) <||> (do (pure ((← (ElemFFR_read e esize)) == 0#1)))
        let result ← (( do
          if (unknown : Bool)
          then
            (do
              if ((←((pure (! fault)) <&&> (do
                   (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA)))) : Bool)
              then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
              else
                (do
                  if ((← (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO)) : Bool)
                  then (do (Elem_set result e esize (Zeros (n := esize))))
                  else (do (Elem_set result e esize (← (Elem_read orig e esize))))))
          else (do (Elem_set result e esize (← (Extend data esize is_unsigned)))) ) : SailM (BitVec VL) )
        (pure (accdesc, data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM (AccessDescriptor × (BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1SB_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVEFF contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:57727.24-57727.25"
  let (accdesc, data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (accdesc, data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (accdesc, data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (accdesc, data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let (accdesc, data, fault) ← (( do
                if (accdesc.first : Bool)
                then
                  (do
                    let data ← (Mem_read addr mbytes accdesc)
                    let accdesc : AccessDescriptor := { accdesc with first := false }
                    (pure (accdesc, data, fault)))
                else
                  (do
                    let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
                    let data : (BitVec msize) := tup__0
                    let fault : Bool := tup__1
                    (pure (accdesc, data, fault))) ) : SailM (AccessDescriptor × (BitVec msize) × Bool) )
              (pure (accdesc, data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (accdesc, data, fault))) ) : SailM (AccessDescriptor × (BitVec msize) × Bool) )
        let faulted : Bool := (faulted || fault)
        if (faulted : Bool)
        then (ElemFFR_set e esize 0#1)
        else (pure ())
        let unknown ← (pure unknown) <||> (do (pure ((← (ElemFFR_read e esize)) == 0#1)))
        let result ← (( do
          if (unknown : Bool)
          then
            (do
              if ((←((pure (! fault)) <&&> (do
                   (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA)))) : Bool)
              then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
              else
                (do
                  if ((← (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO)) : Bool)
                  then (do (Elem_set result e esize (Zeros (n := esize))))
                  else (do (Elem_set result e esize (← (Elem_read orig e esize))))))
          else (do (Elem_set result e esize (← (Extend data esize is_unsigned)))) ) : SailM (BitVec VL) )
        (pure (accdesc, data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM (AccessDescriptor × (BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let (data, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, result) := loop_vars
      loop_vars ← do
        let (data, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let data ← (Mem_read addr mbytes accdesc)
              let result ← (Elem_set result e esize (← (Extend data esize is_unsigned)))
              (pure (data, result)))
          else
            (do
              let result ← (Elem_set result e esize (Zeros (n := esize)))
              (pure (data, result))) ) : SailM ((BitVec msize) × (BitVec VL)) )
        (pure (data, result))
    (pure loop_vars) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let (data, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, result) := loop_vars
      loop_vars ← do
        let (data, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let data ← (Mem_read addr mbytes accdesc)
              let result ← (Elem_set result e esize (← (Extend data esize is_unsigned)))
              (pure (data, result)))
          else
            (do
              let result ← (Elem_set result e esize (Zeros (n := esize)))
              (pure (data, result))) ) : SailM ((BitVec msize) × (BitVec VL)) )
        (pure (data, result))
    (pure loop_vars) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVEFF contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:58030.24-58030.25"
  let (accdesc, data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (accdesc, data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (accdesc, data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (accdesc, data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let (accdesc, data, fault) ← (( do
                if (accdesc.first : Bool)
                then
                  (do
                    let data ← (Mem_read addr mbytes accdesc)
                    let accdesc : AccessDescriptor := { accdesc with first := false }
                    (pure (accdesc, data, fault)))
                else
                  (do
                    let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
                    let data : (BitVec msize) := tup__0
                    let fault : Bool := tup__1
                    (pure (accdesc, data, fault))) ) : SailM (AccessDescriptor × (BitVec msize) × Bool) )
              (pure (accdesc, data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (accdesc, data, fault))) ) : SailM (AccessDescriptor × (BitVec msize) × Bool) )
        let faulted : Bool := (faulted || fault)
        if (faulted : Bool)
        then (ElemFFR_set e esize 0#1)
        else (pure ())
        let unknown ← (pure unknown) <||> (do (pure ((← (ElemFFR_read e esize)) == 0#1)))
        let result ← (( do
          if (unknown : Bool)
          then
            (do
              if ((←((pure (! fault)) <&&> (do
                   (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA)))) : Bool)
              then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
              else
                (do
                  if ((← (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO)) : Bool)
                  then (do (Elem_set result e esize (Zeros (n := esize))))
                  else (do (Elem_set result e esize (← (Elem_read orig e esize))))))
          else (do (Elem_set result e esize (← (Extend data esize is_unsigned)))) ) : SailM (BitVec VL) )
        (pure (accdesc, data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM (AccessDescriptor × (BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVEFF contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:58147.24-58147.25"
  let (accdesc, data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (accdesc, data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (accdesc, data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (accdesc, data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let (accdesc, data, fault) ← (( do
                if (accdesc.first : Bool)
                then
                  (do
                    let data ← (Mem_read addr mbytes accdesc)
                    let accdesc : AccessDescriptor := { accdesc with first := false }
                    (pure (accdesc, data, fault)))
                else
                  (do
                    let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
                    let data : (BitVec msize) := tup__0
                    let fault : Bool := tup__1
                    (pure (accdesc, data, fault))) ) : SailM (AccessDescriptor × (BitVec msize) × Bool) )
              (pure (accdesc, data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (accdesc, data, fault))) ) : SailM (AccessDescriptor × (BitVec msize) × Bool) )
        let faulted : Bool := (faulted || fault)
        if (faulted : Bool)
        then (ElemFFR_set e esize 0#1)
        else (pure ())
        let unknown ← (pure unknown) <||> (do (pure ((← (ElemFFR_read e esize)) == 0#1)))
        let result ← (( do
          if (unknown : Bool)
          then
            (do
              if ((←((pure (! fault)) <&&> (do
                   (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA)))) : Bool)
              then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
              else
                (do
                  if ((← (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO)) : Bool)
                  then (do (Elem_set result e esize (Zeros (n := esize))))
                  else (do (Elem_set result e esize (← (Elem_read orig e esize))))))
          else (do (Elem_set result e esize (← (Extend data esize is_unsigned)))) ) : SailM (BitVec VL) )
        (pure (accdesc, data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM (AccessDescriptor × (BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let (data, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, result) := loop_vars
      loop_vars ← do
        let (data, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let data ← (Mem_read addr mbytes accdesc)
              let result ← (Elem_set result e esize (← (Extend data esize is_unsigned)))
              (pure (data, result)))
          else
            (do
              let result ← (Elem_set result e esize (Zeros (n := esize)))
              (pure (data, result))) ) : SailM ((BitVec msize) × (BitVec VL)) )
        (pure (data, result))
    (pure loop_vars) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVEFF contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:58357.24-58357.25"
  let (accdesc, data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (accdesc, data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (accdesc, data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (accdesc, data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let (accdesc, data, fault) ← (( do
                if (accdesc.first : Bool)
                then
                  (do
                    let data ← (Mem_read addr mbytes accdesc)
                    let accdesc : AccessDescriptor := { accdesc with first := false }
                    (pure (accdesc, data, fault)))
                else
                  (do
                    let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
                    let data : (BitVec msize) := tup__0
                    let fault : Bool := tup__1
                    (pure (accdesc, data, fault))) ) : SailM (AccessDescriptor × (BitVec msize) × Bool) )
              (pure (accdesc, data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (accdesc, data, fault))) ) : SailM (AccessDescriptor × (BitVec msize) × Bool) )
        let faulted : Bool := (faulted || fault)
        if (faulted : Bool)
        then (ElemFFR_set e esize 0#1)
        else (pure ())
        let unknown ← (pure unknown) <||> (do (pure ((← (ElemFFR_read e esize)) == 0#1)))
        let result ← (( do
          if (unknown : Bool)
          then
            (do
              if ((←((pure (! fault)) <&&> (do
                   (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA)))) : Bool)
              then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
              else
                (do
                  if ((← (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO)) : Bool)
                  then (do (Elem_set result e esize (Zeros (n := esize))))
                  else (do (Elem_set result e esize (← (Elem_read orig e esize))))))
          else (do (Elem_set result e esize (← (Extend data esize is_unsigned)))) ) : SailM (BitVec VL) )
        (pure (accdesc, data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM (AccessDescriptor × (BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFB_I_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let offset := offset
  let base := base
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
          let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
          (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFH_I_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let offset := offset
  let base := base
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
          let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
          (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 2 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFW_I_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let offset := offset
  let base := base
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
          let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
          (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 3 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFD_I_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let offset := offset
  let base := base
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
          let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
          (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let (data, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, result) := loop_vars
      loop_vars ← do
        let (data, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let data ← (Mem_read addr mbytes accdesc)
              let result ← (Elem_set result e esize (← (Extend data esize is_unsigned)))
              (pure (data, result)))
          else
            (do
              let result ← (Elem_set result e esize (Zeros (n := esize)))
              (pure (data, result))) ) : SailM ((BitVec msize) × (BitVec VL)) )
        (pure (data, result))
    (pure loop_vars) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (Z_read m VL)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let (data, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, result) := loop_vars
      loop_vars ← do
        let (data, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let off ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offset e esize)) (offs_size -i 1) 0) offs_unsigned)
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let data ← (Mem_read addr mbytes accdesc)
              let result ← (Elem_set result e esize (← (Extend data esize is_unsigned)))
              (pure (data, result)))
          else
            (do
              let result ← (Elem_set result e esize (Zeros (n := esize)))
              (pure (data, result))) ) : SailM ((BitVec msize) × (BitVec VL)) )
        (pure (data, result))
    (pure loop_vars) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL result)


