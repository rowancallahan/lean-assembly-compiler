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

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FADD_Z_P_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (imm : (BitVec esize)) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:56.53-56.54"
            (Elem_set result e esize (← (FPAdd element1 imm (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FSUB_Z_P_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (imm : (BitVec esize)) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:129.53-129.54"
            (Elem_set result e esize (← (FPSub element1 imm (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMUL_Z_P_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (imm : (BitVec esize)) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:202.53-202.54"
            (Elem_set result e esize (← (FPMul element1 imm (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FSUBR_Z_P_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (imm : (BitVec esize)) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:275.53-275.54"
            (Elem_set result e esize (← (FPSub imm element1 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNM_Z_P_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (imm : (BitVec esize)) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:348.53-348.54"
            (Elem_set result e esize (← (FPMaxNum element1 imm (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNM_Z_P_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (imm : (BitVec esize)) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:418.53-418.54"
            (Elem_set result e esize (← (FPMinNum element1 imm (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAX_Z_P_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (imm : (BitVec esize)) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:488.53-488.54"
            (Elem_set result e esize (← (FPMax element1 imm (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMIN_Z_P_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (imm : (BitVec esize)) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:558.53-558.54"
            (Elem_set result e esize (← (FPMin element1 imm (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMGE_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:635.59-635.60"
                  (FPCompareEQ element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:639.59-639.60"
                  (FPCompareGE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:643.59-643.60"
                  (FPCompareGT element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:647.59-647.60"
                  (FPCompareNE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:651.117-651.118"
                  (FPCompareGT (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:655.117-655.118"
                  (FPCompareGE (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | _ => (pure res) ) : SailM Bool )
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMGT_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:738.59-738.60"
                  (FPCompareEQ element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:742.59-742.60"
                  (FPCompareGE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:746.59-746.60"
                  (FPCompareGT element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:750.59-750.60"
                  (FPCompareNE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:754.117-754.118"
                  (FPCompareGT (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:758.117-758.118"
                  (FPCompareGE (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | _ => (pure res) ) : SailM Bool )
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMLT_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:841.59-841.60"
                  (FPCompareEQ element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:845.59-845.60"
                  (FPCompareGE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:849.59-849.60"
                  (FPCompareGT element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:853.59-853.60"
                  (FPCompareNE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:857.117-857.118"
                  (FPCompareGT (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:861.117-861.118"
                  (FPCompareGE (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | _ => (pure res) ) : SailM Bool )
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMLE_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:944.59-944.60"
                  (FPCompareEQ element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:948.59-948.60"
                  (FPCompareGE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:952.59-952.60"
                  (FPCompareGT element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:956.59-956.60"
                  (FPCompareNE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:960.117-960.118"
                  (FPCompareGT (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:964.117-964.118"
                  (FPCompareGE (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | _ => (pure res) ) : SailM Bool )
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMEQ_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:1047.59-1047.60"
                  (FPCompareEQ element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:1051.59-1051.60"
                  (FPCompareGE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:1055.59-1055.60"
                  (FPCompareGT element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:1059.59-1059.60"
                  (FPCompareNE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:1063.117-1063.118"
                  (FPCompareGT (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:1067.117-1067.118"
                  (FPCompareGE (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | _ => (pure res) ) : SailM Bool )
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMNE_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
            let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:1150.59-1150.60"
                  (FPCompareEQ element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:1154.59-1154.60"
                  (FPCompareGE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:1158.59-1158.60"
                  (FPCompareGT element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:1162.59-1162.60"
                  (FPCompareNE element (integer_subrange 0 (esize -i 1) 0) (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:1166.117-1166.118"
                  (FPCompareGT (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "src/instrs64_sve.sail:1170.117-1170.118"
                  (FPCompareGE (integer_subrange 0 (esize -i 1) 0) element (← (FPCR_read ()))))
              | _ => (pure res) ) : SailM Bool )
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FADDA_V_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (V_read dn esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec esize) := operand1
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
            let element ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:1250.53-1250.54"
            (FPAdd result element (← (FPCR_read ()))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec esize) )
  (V_set dn esize result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_D2X (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_D2W (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_S2W (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_S2X (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_Z_P_Z_D2X (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_Z_P_Z_D2W (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_Z_P_Z_S2W (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_Z_P_Z_S2X (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_Z_P_Z_FP162H (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_Z_P_Z_FP162W (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_Z_P_Z_FP162X (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_FP162H (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_FP162W (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_FP162X (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let res ← (( do (FPToFixed (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (← (Extend res esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_H2FP16 (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_W2FP16 (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_X2FP16 (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_Z_P_Z_H2FP16 (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_Z_P_Z_W2FP16 (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_Z_P_Z_X2FP16 (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_D2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
            let res ← (( do (FPConvertSVE__1 (Sail.BitVec.extractLsb element (s_esize -i 1) 0) (← (FPCR_read ())) d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend res esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_D2H (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
            let res ← (( do (FPConvertSVE__1 (Sail.BitVec.extractLsb element (s_esize -i 1) 0) (← (FPCR_read ())) d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend res esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_S2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
            let res ← (( do (FPConvertSVE__1 (Sail.BitVec.extractLsb element (s_esize -i 1) 0) (← (FPCR_read ())) d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend res esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_H2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
            let res ← (( do (FPConvertSVE__1 (Sail.BitVec.extractLsb element (s_esize -i 1) 0) (← (FPCR_read ())) d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend res esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_H2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
            let res ← (( do (FPConvertSVE__1 (Sail.BitVec.extractLsb element (s_esize -i 1) 0) (← (FPCR_read ())) d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend res esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_S2H (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
            let res ← (( do (FPConvertSVE__1 (Sail.BitVec.extractLsb element (s_esize -i 1) 0) (← (FPCR_read ())) d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend res esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRECPE_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3116.49-3116.50"
        (Elem_set result e esize (← (FPRecipEstimate element (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRSQRTE_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3176.49-3176.50"
        (Elem_set result e esize (← (FPRSqrtEstimate element (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRECPX_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3241.53-3241.54"
            (Elem_set result e esize (← (FPRecpX element (← (FPCR_read ()))))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FSQRT_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3310.53-3310.54"
            (Elem_set result e esize (← (FPSqrt element (← (FPCR_read ()))))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_exact : Bool, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTA_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (exact : Bool) (g : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
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
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3379.53-3379.54"
            (Elem_set result e esize (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_exact : Bool, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTI_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (exact : Bool) (g : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
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
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3450.53-3450.54"
            (Elem_set result e esize (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_exact : Bool, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTM_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (exact : Bool) (g : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
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
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3521.53-3521.54"
            (Elem_set result e esize (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_exact : Bool, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTN_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (exact : Bool) (g : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
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
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3592.53-3592.54"
            (Elem_set result e esize (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_exact : Bool, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTP_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (exact : Bool) (g : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
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
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3663.53-3663.54"
            (Elem_set result e esize (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_exact : Bool, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTX_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (exact : Bool) (g : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
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
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3734.53-3734.54"
            (Elem_set result e esize (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_exact : Bool, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTZ_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (exact : Bool) (g : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
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
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:3805.53-3805.54"
            (Elem_set result e esize (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_Z_P_Z_X2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_Z_P_Z_X2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_Z_P_Z_W2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_Z_P_Z_W2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_X2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_X2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_W2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_W2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let fpval ← (( do (FixedToFP (Sail.BitVec.extractLsb element (s_esize -i 1) 0) 0 is_unsigned (← (FPCR_read ())) rounding d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend fpval esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FABD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:4438.53-4438.54"
            (Elem_set result e esize (← (FPAbs (← (FPSub element1 element2 (← (FPCR_read ()))))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:4510.53-4510.54"
            (Elem_set result e esize (← (FPAdd element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FDIV_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:4579.53-4579.54"
            (Elem_set result e esize (← (FPDiv element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FDIVR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:4651.53-4651.54"
            (Elem_set result e esize (← (FPDiv element2 element1 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNM_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:4723.53-4723.54"
            (Elem_set result e esize (← (FPMaxNum element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNM_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:4792.53-4792.54"
            (Elem_set result e esize (← (FPMinNum element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAX_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:4861.53-4861.54"
            (Elem_set result e esize (← (FPMax element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMIN_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:4930.53-4930.54"
            (Elem_set result e esize (← (FPMin element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMUL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:4999.53-4999.54"
            (Elem_set result e esize (← (FPMul element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMULX_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5068.53-5068.54"
            (Elem_set result e esize (← (FPMulX element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FSCALE_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5140.53-5140.54"
            (Elem_set result e esize (← (FPScale element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FSUB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5212.53-5212.54"
            (Elem_set result e esize (← (FPSub element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FSUBR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5281.53-5281.54"
            (Elem_set result e esize (← (FPSub element2 element1 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FADDV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5346.45-5346.46"
  let identity ← (( do (FPZero 0#1 esize) ) : SailM (BitVec esize) )
  (V_set d esize (← (ReducePredicated ReduceOp_FADD operand mask identity)))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNMV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5407.45-5407.46"
  let identity ← (( do (FPDefaultNaN esize) ) : SailM (BitVec esize) )
  (V_set d esize (← (ReducePredicated ReduceOp_FMAXNUM operand mask identity)))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNMV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5468.45-5468.46"
  let identity ← (( do (FPDefaultNaN esize) ) : SailM (BitVec esize) )
  (V_set d esize (← (ReducePredicated ReduceOp_FMINNUM operand mask identity)))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5529.45-5529.46"
  let identity ← (( do (FPInfinity 1#1 esize) ) : SailM (BitVec esize) )
  (V_set d esize (← (ReducePredicated ReduceOp_FMAX operand mask identity)))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMINV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5590.45-5590.46"
  let identity ← (( do (FPInfinity 0#1 esize) ) : SailM (BitVec esize) )
  (V_set d esize (← (ReducePredicated ReduceOp_FMIN operand mask identity)))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FACGE_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
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
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5665.59-5665.60"
                  (FPCompareGE (← (FPAbs element1)) (← (FPAbs element2)) (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5669.59-5669.60"
                  (FPCompareGT (← (FPAbs element1)) (← (FPAbs element2)) (← (FPCR_read ()))))
              | _ => (pure res) ) : SailM Bool )
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FACGT_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
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
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5756.59-5756.60"
                  (FPCompareGE (← (FPAbs element1)) (← (FPAbs element2)) (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5760.59-5760.60"
                  (FPCompareGT (← (FPAbs element1)) (← (FPAbs element2)) (← (FPCR_read ()))))
              | _ => (pure res) ) : SailM Bool )
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMUO_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
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
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5847.59-5847.60"
                  (FPCompareEQ element1 element2 (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5851.59-5851.60"
                  (FPCompareGE element1 element2 (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5855.59-5855.60"
                  (FPCompareGT element1 element2 (← (FPCR_read ()))))
              | .Cmp_UN =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5859.59-5859.60"
                  (FPCompareUN element1 element2 (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5863.59-5863.60"
                  (FPCompareNE element1 element2 (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5867.59-5867.60"
                  (FPCompareGT element2 element1 (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5871.59-5871.60"
                  (FPCompareGE element2 element1 (← (FPCR_read ())))) ) : SailM Bool )
            let res := res
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMGE_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
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
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5958.59-5958.60"
                  (FPCompareEQ element1 element2 (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5962.59-5962.60"
                  (FPCompareGE element1 element2 (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5966.59-5966.60"
                  (FPCompareGT element1 element2 (← (FPCR_read ()))))
              | .Cmp_UN =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5970.59-5970.60"
                  (FPCompareUN element1 element2 (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5974.59-5974.60"
                  (FPCompareNE element1 element2 (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5978.59-5978.60"
                  (FPCompareGT element2 element1 (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:5982.59-5982.60"
                  (FPCompareGE element2 element1 (← (FPCR_read ())))) ) : SailM Bool )
            let res := res
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMGT_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
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
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6071.59-6071.60"
                  (FPCompareEQ element1 element2 (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6075.59-6075.60"
                  (FPCompareGE element1 element2 (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6079.59-6079.60"
                  (FPCompareGT element1 element2 (← (FPCR_read ()))))
              | .Cmp_UN =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6083.59-6083.60"
                  (FPCompareUN element1 element2 (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6087.59-6087.60"
                  (FPCompareNE element1 element2 (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6091.59-6091.60"
                  (FPCompareGT element2 element1 (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6095.59-6095.60"
                  (FPCompareGE element2 element1 (← (FPCR_read ())))) ) : SailM Bool )
            let res := res
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMEQ_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
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
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6184.59-6184.60"
                  (FPCompareEQ element1 element2 (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6188.59-6188.60"
                  (FPCompareGE element1 element2 (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6192.59-6192.60"
                  (FPCompareGT element1 element2 (← (FPCR_read ()))))
              | .Cmp_UN =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6196.59-6196.60"
                  (FPCompareUN element1 element2 (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6200.59-6200.60"
                  (FPCompareNE element1 element2 (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6204.59-6204.60"
                  (FPCompareGT element2 element1 (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6208.59-6208.60"
                  (FPCompareGE element2 element1 (← (FPCR_read ())))) ) : SailM Bool )
            let res := res
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMNE_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
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
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let res ← (( do (undefined_bool ()) ) : SailM Bool )
            let res ← (( do
              match op with
              | .Cmp_EQ =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6297.59-6297.60"
                  (FPCompareEQ element1 element2 (← (FPCR_read ()))))
              | .Cmp_GE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6301.59-6301.60"
                  (FPCompareGE element1 element2 (← (FPCR_read ()))))
              | .Cmp_GT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6305.59-6305.60"
                  (FPCompareGT element1 element2 (← (FPCR_read ()))))
              | .Cmp_UN =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6309.59-6309.60"
                  (FPCompareUN element1 element2 (← (FPCR_read ()))))
              | .Cmp_NE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6313.59-6313.60"
                  (FPCompareNE element1 element2 (← (FPCR_read ()))))
              | .Cmp_LT =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6317.59-6317.60"
                  (FPCompareGT element2 element1 (← (FPCR_read ()))))
              | .Cmp_LE =>
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6321.59-6321.60"
                  (FPCompareGE element2 element1 (← (FPCR_read ())))) ) : SailM Bool )
            let res := res
            let pbit : (BitVec 1) :=
              if (res : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLA_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
            let element1 ← (( do
              if (op1_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6409.57-6409.58"
                  (FPNeg element1))
              else (pure element1) ) : SailM (BitVec esize) )
            let element3 ← (( do
              if (op3_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6413.57-6413.58"
                  (FPNeg element3))
              else (pure element3) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6416.53-6416.54"
            (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize (← (Elem_read operand3 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLS_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
            let element1 ← (( do
              if (op1_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6497.57-6497.58"
                  (FPNeg element1))
              else (pure element1) ) : SailM (BitVec esize) )
            let element3 ← (( do
              if (op3_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6501.57-6501.58"
                  (FPNeg element3))
              else (pure element3) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6504.53-6504.54"
            (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize (← (Elem_read operand3 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FNMLA_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
            let element1 ← (( do
              if (op1_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6585.57-6585.58"
                  (FPNeg element1))
              else (pure element1) ) : SailM (BitVec esize) )
            let element3 ← (( do
              if (op3_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6589.57-6589.58"
                  (FPNeg element3))
              else (pure element3) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6592.53-6592.54"
            (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize (← (Elem_read operand3 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FNMLS_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
            let element1 ← (( do
              if (op1_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6676.57-6676.58"
                  (FPNeg element1))
              else (pure element1) ) : SailM (BitVec esize) )
            let element3 ← (( do
              if (op3_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6680.57-6680.58"
                  (FPNeg element3))
              else (pure element3) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6683.53-6683.54"
            (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize (← (Elem_read operand3 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FMAD_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let operand3 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read a VL)
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
            let element1 ← (( do
              if (op1_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6767.57-6767.58"
                  (FPNeg element1))
              else (pure element1) ) : SailM (BitVec esize) )
            let element3 ← (( do
              if (op3_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6771.57-6771.58"
                  (FPNeg element3))
              else (pure element3) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6774.53-6774.54"
            (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FMSB_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let operand3 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read a VL)
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
            let element1 ← (( do
              if (op1_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6858.57-6858.58"
                  (FPNeg element1))
              else (pure element1) ) : SailM (BitVec esize) )
            let element3 ← (( do
              if (op3_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6862.57-6862.58"
                  (FPNeg element3))
              else (pure element3) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6865.53-6865.54"
            (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FNMAD_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let operand3 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read a VL)
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
            let element1 ← (( do
              if (op1_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6949.57-6949.58"
                  (FPNeg element1))
              else (pure element1) ) : SailM (BitVec esize) )
            let element3 ← (( do
              if (op3_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6953.57-6953.58"
                  (FPNeg element3))
              else (pure element3) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:6956.53-6956.54"
            (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FNMSB_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let operand3 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read a VL)
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
            let element1 ← (( do
              if (op1_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7040.57-7040.58"
                  (FPNeg element1))
              else (pure element1) ) : SailM (BitVec esize) )
            let element3 ← (( do
              if (op3_neg : Bool)
              then
                (do
                  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7044.57-7044.58"
                  (FPNeg element3))
              else (pure element3) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7047.53-7047.54"
            (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FADD_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7120.49-7120.50"
        (Elem_set result e esize (← (FPAdd element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMUL_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7181.49-7181.50"
        (Elem_set result e esize (← (FPMul element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FSUB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7242.49-7242.50"
        (Elem_set result e esize (← (FPSub element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FTSMUL_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
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
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7303.49-7303.50"
        (Elem_set result e esize (← (FPTrigSMul element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRECPS_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7367.49-7367.50"
        (Elem_set result e esize (← (FPRecipStepFused element1 element2)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRSQRTS_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7431.49-7431.50"
        (Elem_set result e esize (← (FPRSqrtStepFused element1 element2)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FTSSEL_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
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
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7495.49-7495.50"
        (Elem_set result e esize (← (FPTrigSSel element1 element2)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FEXPA_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7557.49-7557.50"
        (Elem_set result e esize (← (FPExpA element)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FTMAD_Z_ZZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (m : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
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
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7619.49-7619.50"
        (Elem_set result e esize (← (FPTrigMAdd imm element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_sub_i : Bool, k_sub_r : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FCADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  let acc_i ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let acc_r ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let elt2_i ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let elt2_r ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (acc_i, acc_r, elt2_i, elt2_r, result) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (acc_i, acc_r, elt2_i, elt2_r, result)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (acc_i, acc_r, elt2_i, elt2_r, result) := loop_vars
      loop_vars ← do
        let acc_r ← (Elem_read operand1 ((2 *i p) +i 0) esize)
        let acc_i ← (Elem_read operand1 ((2 *i p) +i 1) esize)
        let (acc_r, elt2_i) ← (( do
          if ((← (ActivePredicateElement mask ((2 *i p) +i 0) esize)) : Bool)
          then
            (do
              let elt2_i ← (Elem_read operand2 ((2 *i p) +i 1) esize)
              let elt2_i ← (( do
                if (sub_i : Bool)
                then
                  (do
                    sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7694.57-7694.58"
                    (FPNeg elt2_i))
                else (pure elt2_i) ) : SailM (BitVec esize) )
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7697.53-7697.54"
              let acc_r ← (FPAdd acc_r elt2_i (← (FPCR_read ())))
              (pure (acc_r, elt2_i)))
          else (pure (acc_r, elt2_i)) ) : SailM ((BitVec esize) × (BitVec esize)) )
        let (acc_i, elt2_r) ← (( do
          if ((← (ActivePredicateElement mask ((2 *i p) +i 1) esize)) : Bool)
          then
            (do
              let elt2_r ← (Elem_read operand2 ((2 *i p) +i 0) esize)
              let elt2_r ← (( do
                if (sub_r : Bool)
                then
                  (do
                    sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7703.57-7703.58"
                    (FPNeg elt2_r))
                else (pure elt2_r) ) : SailM (BitVec esize) )
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7706.53-7706.54"
              let acc_i ← (FPAdd acc_i elt2_r (← (FPCR_read ())))
              (pure (acc_i, elt2_r)))
          else (pure (acc_i, elt2_r)) ) : SailM ((BitVec esize) × (BitVec esize)) )
        let result ← (Elem_set result ((2 *i p) +i 0) esize acc_r)
        let result ← (Elem_set result ((2 *i p) +i 1) esize acc_i)
        (pure (acc_i, acc_r, elt2_i, elt2_r, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_neg_i : Bool, k_neg_r : Bool, sel_a : Nat, sel_b : Nat, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FCMLA_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (neg_i : Bool) (neg_r : Bool) (sel_a : Nat) (sel_b : Nat) : SailM Unit := do
  let addend_i ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let addend_r ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (addend_i, addend_r, result) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (addend_i, addend_r, result)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (addend_i, addend_r, result) := loop_vars
      loop_vars ← do
        let addend_r ← (Elem_read operand3 ((2 *i p) +i 0) esize)
        let addend_i ← (Elem_read operand3 ((2 *i p) +i 1) esize)
        let addend_r ← (( do
          if ((← (ActivePredicateElement mask ((2 *i p) +i 0) esize)) : Bool)
          then
            (do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i p) +i sel_a) esize) ) : SailM (BitVec esize) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i p) +i sel_a) esize) ) : SailM (BitVec esize) )
              let elt2_a ← (( do
                if (neg_r : Bool)
                then
                  (do
                    sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7790.57-7790.58"
                    (FPNeg elt2_a))
                else (pure elt2_a) ) : SailM (BitVec esize) )
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7793.53-7793.54"
              (FPMulAdd addend_r elt1_a elt2_a (← (FPCR_read ()))))
          else (pure addend_r) ) : SailM (BitVec esize) )
        let addend_i ← (( do
          if ((← (ActivePredicateElement mask ((2 *i p) +i 1) esize)) : Bool)
          then
            (do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i p) +i sel_a) esize) ) : SailM (BitVec esize) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i p) +i sel_b) esize) ) : SailM (BitVec esize) )
              let elt2_b ← (( do
                if (neg_i : Bool)
                then
                  (do
                    sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7800.57-7800.58"
                    (FPNeg elt2_b))
                else (pure elt2_b) ) : SailM (BitVec esize) )
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:7803.53-7803.54"
              (FPMulAdd addend_i elt1_a elt2_b (← (FPCR_read ()))))
          else (pure addend_i) ) : SailM (BitVec esize) )
        let result ← (Elem_set result ((2 *i p) +i 0) esize addend_r)
        let result ← (Elem_set result ((2 *i p) +i 1) esize addend_i)
        (pure (addend_i, addend_r, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_neg_i : Bool, k_neg_r : Bool, sel_a : Nat, sel_b : Nat, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FCMLA_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (neg_i : Bool) (neg_r : Bool) (sel_a : Nat) (sel_b : Nat) : SailM Unit := do
  let addend_i ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let addend_r ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let elt1_a ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let elt2_a ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let elt2_b ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let s ← (( do (undefined_int ()) ) : SailM Int )
  let segmentbase ← (( do (undefined_int ()) ) : SailM Int )
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let pairspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase) := loop_vars
      loop_vars ← do
        let segmentbase : Int := (p -i (Nat.mod p pairspersegment))
        let s : Int := (segmentbase +i index)
        let addend_r ← (Elem_read operand3 ((2 *i p) +i 0) esize)
        let addend_i ← (Elem_read operand3 ((2 *i p) +i 1) esize)
        let elt1_a ← (Elem_read operand1 ((2 *i p) +i sel_a) esize)
        let elt2_a ← (( do
          let s := s
          (Elem_read operand2 ((2 *i s) +i sel_a) esize) ) : SailM (BitVec esize) )
        let elt2_b ← (( do
          let s := s
          (Elem_read operand2 ((2 *i s) +i sel_b) esize) ) : SailM (BitVec esize) )
        let elt2_a ← (( do
          if (neg_r : Bool)
          then (do (FPNeg elt2_a))
          else (pure elt2_a) ) : SailM (BitVec esize) )
        let elt2_b ← (( do
          if (neg_i : Bool)
          then (do (FPNeg elt2_b))
          else (pure elt2_b) ) : SailM (BitVec esize) )
        let addend_r ← (FPMulAdd addend_r elt1_a elt2_a (← (FPCR_read ())))
        let addend_i ← (FPMulAdd addend_i elt1_a elt2_b (← (FPCR_read ())))
        let result ← (Elem_set result ((2 *i p) +i 0) esize addend_r)
        let result ← (Elem_set result ((2 *i p) +i 1) esize addend_i)
        (pure (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec VL) × Int × Int) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_neg_i : Bool, k_neg_r : Bool, sel_a : Nat, sel_b : Nat, List.elem sel_b [0, 1] ∧ List.elem sel_a [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FCMLA_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (neg_i : Bool) (neg_r : Bool) (sel_a : Nat) (sel_b : Nat) : SailM Unit := do
  let addend_i ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let addend_r ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let elt1_a ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let elt2_a ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let elt2_b ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let s ← (( do (undefined_int ()) ) : SailM Int )
  let segmentbase ← (( do (undefined_int ()) ) : SailM Int )
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (2 *i esize))
  let pairspersegment := (Int.ediv 128 (2 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase) := loop_vars
      loop_vars ← do
        let segmentbase : Int := (p -i (Nat.mod p pairspersegment))
        let s : Int := (segmentbase +i index)
        let addend_r ← (Elem_read operand3 ((2 *i p) +i 0) esize)
        let addend_i ← (Elem_read operand3 ((2 *i p) +i 1) esize)
        let elt1_a ← (Elem_read operand1 ((2 *i p) +i sel_a) esize)
        let elt2_a ← (( do
          let s := s
          (Elem_read operand2 ((2 *i s) +i sel_a) esize) ) : SailM (BitVec esize) )
        let elt2_b ← (( do
          let s := s
          (Elem_read operand2 ((2 *i s) +i sel_b) esize) ) : SailM (BitVec esize) )
        let elt2_a ← (( do
          if (neg_r : Bool)
          then (do (FPNeg elt2_a))
          else (pure elt2_a) ) : SailM (BitVec esize) )
        let elt2_b ← (( do
          if (neg_i : Bool)
          then (do (FPNeg elt2_b))
          else (pure elt2_b) ) : SailM (BitVec esize) )
        let addend_r ← (FPMulAdd addend_r elt1_a elt2_a (← (FPCR_read ())))
        let addend_i ← (FPMulAdd addend_i elt1_a elt2_b (← (FPCR_read ())))
        let result ← (Elem_set result ((2 *i p) +i 0) esize addend_r)
        let result ← (Elem_set result ((2 *i p) +i 1) esize addend_i)
        (pure (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec VL) × Int × Int) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMUL_Z_ZZi_H (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize (← (FPMul element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLA_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
        let element3 ← (( do (Elem_read result e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec esize) )
        let element3 ← (( do
          if (op3_neg : Bool)
          then (do (FPNeg element3))
          else (pure element3) ) : SailM (BitVec esize) )
        (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLS_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
        let element3 ← (( do (Elem_read result e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec esize) )
        let element3 ← (( do
          if (op3_neg : Bool)
          then (do (FPNeg element3))
          else (pure element3) ) : SailM (BitVec esize) )
        (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMUL_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize (← (FPMul element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLA_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
        let element3 ← (( do (Elem_read result e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec esize) )
        let element3 ← (( do
          if (op3_neg : Bool)
          then (do (FPNeg element3))
          else (pure element3) ) : SailM (BitVec esize) )
        (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLS_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
        let element3 ← (( do (Elem_read result e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec esize) )
        let element3 ← (( do
          if (op3_neg : Bool)
          then (do (FPNeg element3))
          else (pure element3) ) : SailM (BitVec esize) )
        (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMUL_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize (← (FPMul element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLA_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
        let element3 ← (( do (Elem_read result e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec esize) )
        let element3 ← (( do
          if (op3_neg : Bool)
          then (do (FPNeg element3))
          else (pure element3) ) : SailM (BitVec esize) )
        (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLS_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
        let element3 ← (( do (Elem_read result e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec esize) )
        let element3 ← (( do
          if (op3_neg : Bool)
          then (do (FPNeg element3))
          else (pure element3) ) : SailM (BitVec esize) )
        (Elem_set result e esize (← (FPMulAdd element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FADDP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
  let result ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let element1 ← (Elem_read operand1 (e +i 0) esize)
                    let element2 ← (Elem_read operand1 (e +i 1) esize)
                    (pure (element1, element2)))
                else
                  (do
                    let element1 ← (Elem_read operand2 (e -i 1) esize)
                    let element2 ← (Elem_read operand2 (e +i 0) esize)
                    (pure (element1, element2))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:8726.53-8726.54"
              let result ← (Elem_set result e esize (← (FPAdd element1 element2 (← (FPCR_read ())))))
              (pure (element1, element2, result)))
          else (pure (element1, element2, result)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNMP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
  let result ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let element1 ← (Elem_read operand1 (e +i 0) esize)
                    let element2 ← (Elem_read operand1 (e +i 1) esize)
                    (pure (element1, element2)))
                else
                  (do
                    let element1 ← (Elem_read operand2 (e -i 1) esize)
                    let element2 ← (Elem_read operand2 (e +i 0) esize)
                    (pure (element1, element2))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:8804.53-8804.54"
              let result ← (Elem_set result e esize (← (FPMaxNum element1 element2 (← (FPCR_read ())))))
              (pure (element1, element2, result)))
          else (pure (element1, element2, result)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
  let result ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let element1 ← (Elem_read operand1 (e +i 0) esize)
                    let element2 ← (Elem_read operand1 (e +i 1) esize)
                    (pure (element1, element2)))
                else
                  (do
                    let element1 ← (Elem_read operand2 (e -i 1) esize)
                    let element2 ← (Elem_read operand2 (e +i 0) esize)
                    (pure (element1, element2))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:8882.53-8882.54"
              let result ← (Elem_set result e esize (← (FPMax element1 element2 (← (FPCR_read ())))))
              (pure (element1, element2, result)))
          else (pure (element1, element2, result)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNMP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
  let result ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let element1 ← (Elem_read operand1 (e +i 0) esize)
                    let element2 ← (Elem_read operand1 (e +i 1) esize)
                    (pure (element1, element2)))
                else
                  (do
                    let element1 ← (Elem_read operand2 (e -i 1) esize)
                    let element2 ← (Elem_read operand2 (e +i 0) esize)
                    (pure (element1, element2))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:8960.53-8960.54"
              let result ← (Elem_set result e esize (← (FPMinNum element1 element2 (← (FPCR_read ())))))
              (pure (element1, element2, result)))
          else (pure (element1, element2, result)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
  let result ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2, result) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let element1 ← (Elem_read operand1 (e +i 0) esize)
                    let element2 ← (Elem_read operand1 (e +i 1) esize)
                    (pure (element1, element2)))
                else
                  (do
                    let element1 ← (Elem_read operand2 (e -i 1) esize)
                    let element2 ← (Elem_read operand2 (e +i 0) esize)
                    (pure (element1, element2))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:9038.53-9038.54"
              let result ← (Elem_set result e esize (← (FPMin element1 element2 (← (FPCR_read ())))))
              (pure (element1, element2, result)))
          else (pure (element1, element2, result)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLALB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (← (FPMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLALT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (← (FPMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSLB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 0) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (← (FPMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSLT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (← (FPMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLALB_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
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
        let s := ((2 *i segmentbase) +i index)
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 s (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (← (FPMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLALT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
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
        let s := ((2 *i segmentbase) +i index)
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 s (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (← (FPMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSLB_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
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
        let s := ((2 *i segmentbase) +i index)
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 s (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (← (FPMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSLT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
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
        let s := ((2 *i segmentbase) +i index)
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element2 ← (( do (Elem_read operand2 s (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
        let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec (esize / 2)) )
        (Elem_set result e esize (← (FPMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLALB_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
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
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        (Elem_set result e 32 (← (BFMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLALT_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
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
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        (Elem_set result e 32 (← (BFMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSLB_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
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
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (BFNeg element1))
          else (pure element1) ) : SailM (BitVec 16) )
        (Elem_set result e 32 (← (BFMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSLT_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
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
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (BFNeg element1))
          else (pure element1) ) : SailM (BitVec 16) )
        (Elem_set result e 32 (← (BFMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLALB_Z_ZZZi__ (VL : Nat) (da : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
  let eltspersegment := (Int.ediv 128 32)
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
        let s := ((2 *i segmentbase) +i index)
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        (Elem_set result e 32 (← (BFMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLALT_Z_ZZZi__ (VL : Nat) (da : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
  let eltspersegment := (Int.ediv 128 32)
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
        let s := ((2 *i segmentbase) +i index)
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        (Elem_set result e 32 (← (BFMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSLB_Z_ZZZi__ (VL : Nat) (da : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
  let eltspersegment := (Int.ediv 128 32)
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
        let s := ((2 *i segmentbase) +i index)
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (BFNeg element1))
          else (pure element1) ) : SailM (BitVec 16) )
        (Elem_set result e 32 (← (BFMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSLT_Z_ZZZi__ (VL : Nat) (da : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
  let eltspersegment := (Int.ediv 128 32)
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
        let s := ((2 *i segmentbase) +i index)
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (BFNeg element1))
          else (pure element1) ) : SailM (BitVec 16) )
        (Elem_set result e 32 (← (BFMulAddH element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFDOT_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
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
        let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let sum ← (( do (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
        (Elem_set result e 32 sum)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFDOT_Z_ZZZi__ (VL : Nat) (da : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
  let eltspersegment := (Int.ediv 128 32)
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
        let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16) )
        let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16) )
        let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let sum ← (( do (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
        (Elem_set result e 32 sum)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FDOT_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
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
        let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let sum ← (( do (FPDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
        (Elem_set result e 32 sum)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FDOT_Z_ZZZi__ (VL : Nat) (da : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
  let eltspersegment := (Int.ediv 128 32)
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
        let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16) )
        let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16) )
        let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let sum ← (( do (FPDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
        (Elem_set result e 32 sum)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCVT_Z_P_Z_S2BF (VL : Nat) (d : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask 32)) : Bool)
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
        if ((← (ActivePredicateElement mask e 32)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            let result ← (Elem_set result (2 *i e) 16 (← (FPConvertBF__1 element (← (FPCR_read ())))))
            (Elem_set result ((2 *i e) +i 1) 16 (Zeros (n := 16))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCVTNT_Z_P_Z_S2BF (VL : Nat) (d : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 32)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask 32)) : Bool)
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
        if ((← (ActivePredicateElement mask e 32)) : Bool)
        then
          (do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (Elem_set result ((2 *i e) +i 1) 16 (← (FPConvertBF__1 element (← (FPCR_read ()))))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMMLA_Z_ZZZ_S (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL (4 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let op1 ← (( do (undefined_bitvector (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
  let op2 ← (( do (undefined_bitvector (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
  let addend ← (( do (undefined_bitvector (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
  let res ← (( do (undefined_bitvector (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := (addend, op1, op2, res, result)
    for s in [loop_s_lower:loop_s_upper:1]i do
      let (addend, op1, op2, res, result) := loop_vars
      loop_vars ← do
        let op1 ← (Elem_read operand1 s (4 *i esize))
        let op2 ← (Elem_read operand2 s (4 *i esize))
        let addend ← (Elem_read operand3 s (4 *i esize))
        let res ← (FPMatMulAdd addend op1 op2 esize (← (FPCR_read ())))
        let result ← (Elem_set result s (4 *i esize) res)
        (pure (addend, op1, op2, res, result))
    (pure loop_vars) ) : SailM ((BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMMLA_Z_ZZZ_D (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  if ((VL <b (esize *i 4)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let segments := (Int.ediv VL (4 *i esize))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let op1 ← (( do (undefined_bitvector (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
  let op2 ← (( do (undefined_bitvector (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
  let addend ← (( do (undefined_bitvector (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
  let res ← (( do (undefined_bitvector (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower := 0
    let loop_s_upper := (segments -i 1)
    let mut loop_vars := (addend, op1, op2, res, result)
    for s in [loop_s_lower:loop_s_upper:1]i do
      let (addend, op1, op2, res, result) := loop_vars
      loop_vars ← do
        let op1 ← (Elem_read operand1 s (4 *i esize))
        let op2 ← (Elem_read operand2 s (4 *i esize))
        let addend ← (Elem_read operand3 s (4 *i esize))
        let res ← (FPMatMulAdd addend op1 op2 esize (← (FPCR_read ())))
        let result ← (Elem_set result s (4 *i esize) res)
        (pure (addend, op1, op2, res, result))
    (pure loop_vars) ) : SailM ((BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let segments := (Int.ediv VL 128)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
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
        let res ← (BFMatMulAdd addend op1 op2)
        let result ← (Elem_set result s 128 res)
        (pure (addend, op1, op2, res, result))
    (pure loop_vars) ) : SailM ((BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec VL)) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FLOGB_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:10809.53-10809.54"
            (Elem_set result e esize (← (FPLogB element (← (FPCR_read ()))))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTNT_Z_P_Z_D2S (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
            (Elem_set result ((2 *i e) +i 1) (Int.ediv esize 2) (← (FPConvertSVE__1 element (← (FPCR_read ())) (Int.ediv esize 2)))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTNT_Z_P_Z_S2H (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
            (Elem_set result ((2 *i e) +i 1) (Int.ediv esize 2) (← (FPConvertSVE__1 element (← (FPCR_read ())) (Int.ediv esize 2)))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTLT_Z_P_Z_S2D (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
            let element ← (( do (Elem_read operand ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
            (Elem_set result e esize (← (FPConvertSVE__1 element (← (FPCR_read ())) esize))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTLT_Z_P_Z_H2S (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
            let element ← (( do (Elem_read operand ((2 *i e) +i 1) (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
            (Elem_set result e esize (← (FPConvertSVE__1 element (← (FPCR_read ())) esize))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTX_Z_P_Z_D2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
            let res ← (( do (FPConvertSVE (Sail.BitVec.extractLsb element (s_esize -i 1) 0) (← (FPCR_read ())) FPRounding_ODD d_esize) ) : SailM (BitVec d_esize) )
            (Elem_set result e esize (Sail.BitVec.zeroExtend res esize)))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTXNT_Z_P_Z_D2S (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
            (Elem_set result ((2 *i e) +i 1) (Int.ediv esize 2) (← (FPConvertSVE element (← (FPCR_read ())) FPRounding_ODD (Int.ediv esize 2)))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCLAMP_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
        let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:11265.49-11265.50"
        (Elem_set result e esize (← (FPMinNum (← (FPMaxNum element1 element3 (← (FPCR_read ())))) element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FADDQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:11326.45-11326.46"
  let identity ← (( do (FPZero 0#1 esize) ) : SailM (BitVec esize) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let p2bits ← do (CeilPow2 (segments *i esize))
  let p2elems := (Int.ediv p2bits esize)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let stmp ← (( do (undefined_bitvector p2bits) ) : SailM (BitVec p2bits) )
        let stmp ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (p2elems -i 1)
          let mut loop_vars_1 := stmp
          for s in [loop_s_lower:loop_s_upper:1]i do
            let stmp := loop_vars_1
            loop_vars_1 ← do
              if ((←((pure (s <b segments)) <&&> (do
                   (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)))) : Bool)
              then (do (Elem_set stmp s esize (← (Elem_read operand ((s *i elempersegment) +i e) esize))))
              else (do (Elem_set stmp s esize identity))
          (pure loop_vars_1) ) : SailM (BitVec p2bits) )
        sail_assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && (p2bits ≥b esize)) || (! (((esize == 16) || (esize == 32)) || (esize == 64)))) "src/instrs64_sve.sail:11340.129-11340.130"
        let dtmp ← (( do (Reduce ReduceOp_FADD stmp esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize dtmp)
    (pure loop_vars) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNMQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:11405.45-11405.46"
  let identity ← (( do (FPDefaultNaN esize) ) : SailM (BitVec esize) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let p2bits ← do (CeilPow2 (segments *i esize))
  let p2elems := (Int.ediv p2bits esize)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let stmp ← (( do (undefined_bitvector p2bits) ) : SailM (BitVec p2bits) )
        let stmp ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (p2elems -i 1)
          let mut loop_vars_1 := stmp
          for s in [loop_s_lower:loop_s_upper:1]i do
            let stmp := loop_vars_1
            loop_vars_1 ← do
              if ((←((pure (s <b segments)) <&&> (do
                   (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)))) : Bool)
              then (do (Elem_set stmp s esize (← (Elem_read operand ((s *i elempersegment) +i e) esize))))
              else (do (Elem_set stmp s esize identity))
          (pure loop_vars_1) ) : SailM (BitVec p2bits) )
        sail_assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && (p2bits ≥b esize)) || (! (((esize == 16) || (esize == 32)) || (esize == 64)))) "src/instrs64_sve.sail:11419.129-11419.130"
        let dtmp ← (( do (Reduce ReduceOp_FMAXNUM stmp esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize dtmp)
    (pure loop_vars) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNMQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:11484.45-11484.46"
  let identity ← (( do (FPDefaultNaN esize) ) : SailM (BitVec esize) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let p2bits ← do (CeilPow2 (segments *i esize))
  let p2elems := (Int.ediv p2bits esize)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let stmp ← (( do (undefined_bitvector p2bits) ) : SailM (BitVec p2bits) )
        let stmp ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (p2elems -i 1)
          let mut loop_vars_1 := stmp
          for s in [loop_s_lower:loop_s_upper:1]i do
            let stmp := loop_vars_1
            loop_vars_1 ← do
              if ((←((pure (s <b segments)) <&&> (do
                   (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)))) : Bool)
              then (do (Elem_set stmp s esize (← (Elem_read operand ((s *i elempersegment) +i e) esize))))
              else (do (Elem_set stmp s esize identity))
          (pure loop_vars_1) ) : SailM (BitVec p2bits) )
        sail_assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && (p2bits ≥b esize)) || (! (((esize == 16) || (esize == 32)) || (esize == 64)))) "src/instrs64_sve.sail:11498.129-11498.130"
        let dtmp ← (( do (Reduce ReduceOp_FMINNUM stmp esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize dtmp)
    (pure loop_vars) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:11563.45-11563.46"
  let identity ← (( do (FPInfinity 1#1 esize) ) : SailM (BitVec esize) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let p2bits ← do (CeilPow2 (segments *i esize))
  let p2elems := (Int.ediv p2bits esize)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let stmp ← (( do (undefined_bitvector p2bits) ) : SailM (BitVec p2bits) )
        let stmp ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (p2elems -i 1)
          let mut loop_vars_1 := stmp
          for s in [loop_s_lower:loop_s_upper:1]i do
            let stmp := loop_vars_1
            loop_vars_1 ← do
              if ((←((pure (s <b segments)) <&&> (do
                   (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)))) : Bool)
              then (do (Elem_set stmp s esize (← (Elem_read operand ((s *i elempersegment) +i e) esize))))
              else (do (Elem_set stmp s esize identity))
          (pure loop_vars_1) ) : SailM (BitVec p2bits) )
        sail_assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && (p2bits ≥b esize)) || (! (((esize == 16) || (esize == 32)) || (esize == 64)))) "src/instrs64_sve.sail:11577.129-11577.130"
        let dtmp ← (( do (Reduce ReduceOp_FMAX stmp esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize dtmp)
    (pure loop_vars) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMINQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:11642.45-11642.46"
  let identity ← (( do (FPInfinity 0#1 esize) ) : SailM (BitVec esize) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let p2bits ← do (CeilPow2 (segments *i esize))
  let p2elems := (Int.ediv p2bits esize)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elempersegment -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let stmp ← (( do (undefined_bitvector p2bits) ) : SailM (BitVec p2bits) )
        let stmp ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (p2elems -i 1)
          let mut loop_vars_1 := stmp
          for s in [loop_s_lower:loop_s_upper:1]i do
            let stmp := loop_vars_1
            loop_vars_1 ← do
              if ((←((pure (s <b segments)) <&&> (do
                   (ActivePredicateElement mask ((s *i elempersegment) +i e) esize)))) : Bool)
              then (do (Elem_set stmp s esize (← (Elem_read operand ((s *i elempersegment) +i e) esize))))
              else (do (Elem_set stmp s esize identity))
          (pure loop_vars_1) ) : SailM (BitVec p2bits) )
        sail_assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && (p2bits ≥b esize)) || (! (((esize == 16) || (esize == 32)) || (esize == 64)))) "src/instrs64_sve.sail:11656.129-11656.130"
        let dtmp ← (( do (Reduce ReduceOp_FMIN stmp esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize dtmp)
    (pure loop_vars) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFADD_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
        (Elem_set result e 16 (← (BFAdd element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFMUL_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
        (Elem_set result e 16 (← (BFMul element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFSUB_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
        (Elem_set result e 16 (← (BFSub element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        if ((← (ActivePredicateElement mask e 16)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (Elem_set result e 16 (← (BFAdd element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e 16 element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMUL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        if ((← (ActivePredicateElement mask e 16)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (Elem_set result e 16 (← (BFMul element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e 16 element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFSUB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        if ((← (ActivePredicateElement mask e 16)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (Elem_set result e 16 (← (BFSub element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e 16 element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, da : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLA_Z_P_ZZZ__ (VL : Nat) (da : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e 16)) : Bool)
        then
          (do
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
            let element1 ← (( do
              if (op1_neg : Bool)
              then (do (BFNeg element1))
              else (pure element1) ) : SailM (BitVec 16) )
            let element3 ← (( do
              if (op3_neg : Bool)
              then (do (BFNeg element3))
              else (pure element3) ) : SailM (BitVec 16) )
            (Elem_set result e 16 (← (BFMulAdd element3 element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e 16 (← (Elem_read operand3 e 16))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLS_Z_P_ZZZ__ (VL : Nat) (da : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
    then (Z_read m VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e 16)) : Bool)
        then
          (do
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
            let element1 ← (( do
              if (op1_neg : Bool)
              then (do (BFNeg element1))
              else (pure element1) ) : SailM (BitVec 16) )
            let element3 ← (( do
              if (op3_neg : Bool)
              then (do (BFNeg element3))
              else (pure element3) ) : SailM (BitVec 16) )
            (Elem_set result e 16 (← (BFMulAdd element3 element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e 16 (← (Elem_read operand3 e 16))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLA_Z_ZZZi_H (VL : Nat) (da : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let eltspersegment := (Int.ediv 128 16)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read result e 16) ) : SailM (BitVec 16) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (BFNeg element1))
          else (pure element1) ) : SailM (BitVec 16) )
        let element3 ← (( do
          if (op3_neg : Bool)
          then (do (BFNeg element3))
          else (pure element3) ) : SailM (BitVec 16) )
        (Elem_set result e 16 (← (BFMulAdd element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLS_Z_ZZZi_H (VL : Nat) (da : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let eltspersegment := (Int.ediv 128 16)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read result e 16) ) : SailM (BitVec 16) )
        let element1 ← (( do
          if (op1_neg : Bool)
          then (do (BFNeg element1))
          else (pure element1) ) : SailM (BitVec 16) )
        let element3 ← (( do
          if (op3_neg : Bool)
          then (do (BFNeg element3))
          else (pure element3) ) : SailM (BitVec 16) )
        (Elem_set result e 16 (← (BFMulAdd element3 element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFMUL_Z_ZZi_H (VL : Nat) (d : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let eltspersegment := (Int.ediv 128 16)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
        (Elem_set result e 16 (← (BFMul element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMAXNM_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        if ((← (ActivePredicateElement mask e 16)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (Elem_set result e 16 (← (BFMaxNum element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e 16 element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMINNM_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        if ((← (ActivePredicateElement mask e 16)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (Elem_set result e 16 (← (BFMinNum element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e 16 element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMAX_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        if ((← (ActivePredicateElement mask e 16)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (Elem_set result e 16 (← (BFMax element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e 16 element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMIN_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do
    if ((← (AnyActiveElement mask 16)) : Bool)
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
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        if ((← (ActivePredicateElement mask e 16)) : Bool)
        then
          (do
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (Elem_set result e 16 (← (BFMin element1 element2 (← (FPCR_read ()))))))
        else (do (Elem_set result e 16 element1))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCLAMP_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 16)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
        let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
        (Elem_set result e 16 (← (BFMinNum (← (BFMaxNum element1 element3 (← (FPCR_read ())))) element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, mbytes : Nat, n : Nat, osize : Nat, osize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem mbytes [1, 2, 4, 8] ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADR_Z_AZ_D_u32_scaled (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (mbytes : Nat) (n : Nat) (osize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let base ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let offs ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let addr ← (( do (Elem_read base e esize) ) : SailM (BitVec esize) )
        let offset ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offs e esize)) (osize -i 1) 0) is_unsigned)
        (Elem_set result e esize (BitVec.addInt addr (offset *i mbytes)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, mbytes : Nat, n : Nat, osize : Nat, osize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem mbytes [1, 2, 4, 8] ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADR_Z_AZ_D_s32_scaled (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (mbytes : Nat) (n : Nat) (osize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let base ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let offs ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let addr ← (( do (Elem_read base e esize) ) : SailM (BitVec esize) )
        let offset ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offs e esize)) (osize -i 1) 0) is_unsigned)
        (Elem_set result e esize (BitVec.addInt addr (offset *i mbytes)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, mbytes : Nat, n : Nat, osize : Nat, List.elem osize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem mbytes [1, 2, 4, 8] ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADR_Z_AZ_SD_same_scaled (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (mbytes : Nat) (n : Nat) (osize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let base ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let offs ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let addr ← (( do (Elem_read base e esize) ) : SailM (BitVec esize) )
        sail_assert ((osize -i 1) <b esize) "src/instrs64_sve.sail:12914.46-12914.47"
        let offset ← do (asl_Int (Sail.BitVec.extractLsb (← (Elem_read offs e esize)) (osize -i 1) 0) is_unsigned)
        (Elem_set result e esize (BitVec.addInt addr (offset *i mbytes)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ADD_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize (BitVec.addInt element1 imm))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SUB_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
        (Elem_set result e esize (BitVec.subInt element1 imm))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SUBR_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) : SailM Unit := do
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
        let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        (Elem_set result e esize (integer_subrange (imm -i element1) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_MUL_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) : SailM Unit := do
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
        let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        (Elem_set result e esize (integer_subrange (element1 *i imm) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
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
        (Elem_set result e esize (integer_subrange (Max.max element1 imm) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAX_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
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
        (Elem_set result e esize (integer_subrange (Max.max element1 imm) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMIN_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
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
        (Elem_set result e esize (integer_subrange (Min.min element1 imm) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMIN_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
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
        (Elem_set result e esize (integer_subrange (Min.min element1 imm) (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, imm : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADDPL_R_RI__ (VL : Nat) (d : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let result : (BitVec 64) := (BitVec.addInt operand1 (imm *i (Int.ediv PL 8)))
  if ((d == 31) : Bool)
  then (SP_set result)
  else (X_set d 64 result)

/-- Type quantifiers: VL : Nat, d : Nat, imm : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADDVL_R_RI__ (VL : Nat) (d : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let result : (BitVec 64) := (BitVec.addInt operand1 (imm *i (Int.ediv VL 8)))
  if ((d == 31) : Bool)
  then (SP_set result)
  else (X_set d 64 result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADD_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
        (Elem_set result e esize (element1 + element2))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_AND_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  (Z_set d VL (operand1 &&& operand2))

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BIC_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  (Z_set d VL (operand1 &&& (Complement.complement operand2)))

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_EOR_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  (Z_set d VL (operand1 ^^^ operand2))

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ORR_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  (Z_set d VL (operand1 ||| operand2))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
        (Elem_set result e esize (element1 - element2))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        then (do (Elem_set result e esize (element1 + element2)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_AND_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        then (do (Elem_set result e esize (element1 &&& element2)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BIC_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        then (do (Elem_set result e esize (element1 &&& (Complement.complement element2))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_EOR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        then (do (Elem_set result e esize (element1 ^^^ element2)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_LSL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let shift := (Min.min (BitVec.toNat element2) esize)
            (Elem_set result e esize (element1 <<< shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_LSLR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let shift := (Min.min (BitVec.toNat element1) esize)
            (Elem_set result e esize (element2 <<< shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_MUL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
            let product := (element1 *i element2)
            (Elem_set result e esize (integer_subrange product (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ORR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        then (do (Elem_set result e esize (element1 ||| element2)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SUB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        then (do (Elem_set result e esize (element1 - element2)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SUBR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
        then (do (Elem_set result e esize (element2 - element1)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_LSR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let shift := (Min.min (BitVec.toNat element2) esize)
            (Elem_set result e esize (element1 >>> shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ASR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let shift := (Min.min (BitVec.toNat element2) esize)
            (Elem_set result e esize (BitVec.sshiftRight element1 shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_LSRR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let shift := (Min.min (BitVec.toNat element1) esize)
            (Elem_set result e esize (element2 >>> shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ASRR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
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
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let shift := (Min.min (BitVec.toNat element1) esize)
            (Elem_set result e esize (BitVec.sshiftRight element2 shift)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UABD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let absdiff := (Int.natAbs (element1 -i element2))
            (Elem_set result e esize (integer_subrange absdiff (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SABD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let absdiff := (Int.natAbs (element1 -i element2))
            (Elem_set result e esize (integer_subrange absdiff (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UDIV_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let quotient ← (( do (undefined_int ()) ) : SailM Int )
            let quotient : Int :=
              if ((element2 == 0) : Bool)
              then 0
              else (RoundTowardsZero (div_real (to_real element1) (to_real element2)))
            let quotient := quotient
            (Elem_set result e esize (integer_subrange quotient (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SDIV_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let quotient ← (( do (undefined_int ()) ) : SailM Int )
            let quotient : Int :=
              if ((element2 == 0) : Bool)
              then 0
              else (RoundTowardsZero (div_real (to_real element1) (to_real element2)))
            let quotient := quotient
            (Elem_set result e esize (integer_subrange quotient (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UDIVR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let quotient ← (( do (undefined_int ()) ) : SailM Int )
            let quotient : Int :=
              if ((element1 == 0) : Bool)
              then 0
              else (RoundTowardsZero (div_real (to_real element2) (to_real element1)))
            let quotient := quotient
            (Elem_set result e esize (integer_subrange quotient (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SDIVR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let quotient ← (( do (undefined_int ()) ) : SailM Int )
            let quotient : Int :=
              if ((element1 == 0) : Bool)
              then 0
              else (RoundTowardsZero (div_real (to_real element2) (to_real element1)))
            let quotient := quotient
            (Elem_set result e esize (integer_subrange quotient (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let maximum := (Max.max element1 element2)
            (Elem_set result e esize (integer_subrange maximum (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAX_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let maximum := (Max.max element1 element2)
            (Elem_set result e esize (integer_subrange maximum (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMIN_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let minimum := (Min.min element1 element2)
            (Elem_set result e esize (integer_subrange minimum (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMIN_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let minimum := (Min.min element1 element2)
            (Elem_set result e esize (integer_subrange minimum (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMULH_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let product := (Int.shiftr (element1 *i element2) esize)
            (Elem_set result e esize (integer_subrange product (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMULH_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let product := (Int.shiftr (element1 *i element2) esize)
            (Elem_set result e esize (integer_subrange product (esize -i 1) 0)))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, List.elem rsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELO_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec PL) := (Ones (n := PL))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
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
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec PL)) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, List.elem rsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELS_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec PL) := (Ones (n := PL))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
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
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec PL)) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, List.elem rsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELT_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec PL) := (Ones (n := PL))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
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
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec PL)) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, List.elem rsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELE_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec PL) := (Ones (n := PL))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
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
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec PL)) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, List.elem rsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHI_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec PL) := (Ones (n := PL))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
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
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec PL)) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, List.elem rsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHS_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec PL) := (Ones (n := PL))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
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
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec PL)) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, List.elem rsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGT_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec PL) := (Ones (n := PL))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
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
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec PL)) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, rsize : Nat, List.elem rsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEGE_P_P_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask : (BitVec PL) := (Ones (n := PL))
  let operand1 ← (( do (X_read n rsize) ) : SailM (BitVec rsize) )
  let operand2 ← (( do (X_read m rsize) ) : SailM (BitVec rsize) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let last : Bool := true
  let psize := (Int.ediv esize 8)
  let (last, operand1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
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
    (pure loop_vars) ) : SailM (Bool × (BitVec rsize) × (BitVec PL)) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPEQ_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == imm)
              | .Cmp_NE => (element1 != imm)
              | .Cmp_GE => (element1 ≥b imm)
              | .Cmp_LT => (element1 <b imm)
              | .Cmp_GT => (element1 >b imm)
              | .Cmp_LE => (element1 ≤b imm)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPNE_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == imm)
              | .Cmp_NE => (element1 != imm)
              | .Cmp_GE => (element1 ≥b imm)
              | .Cmp_LT => (element1 <b imm)
              | .Cmp_GT => (element1 >b imm)
              | .Cmp_LE => (element1 ≤b imm)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ imm ∧ imm ≤ 127 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPHS_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == imm)
              | .Cmp_NE => (element1 != imm)
              | .Cmp_GE => (element1 ≥b imm)
              | .Cmp_LT => (element1 <b imm)
              | .Cmp_GT => (element1 >b imm)
              | .Cmp_LE => (element1 ≤b imm)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ imm ∧ imm ≤ 127 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPHI_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == imm)
              | .Cmp_NE => (element1 != imm)
              | .Cmp_GE => (element1 ≥b imm)
              | .Cmp_LT => (element1 <b imm)
              | .Cmp_GT => (element1 >b imm)
              | .Cmp_LE => (element1 ≤b imm)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ imm ∧ imm ≤ 127 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPLO_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == imm)
              | .Cmp_NE => (element1 != imm)
              | .Cmp_GE => (element1 ≥b imm)
              | .Cmp_LT => (element1 <b imm)
              | .Cmp_GT => (element1 >b imm)
              | .Cmp_LE => (element1 ≤b imm)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ imm ∧ imm ≤ 127 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPLS_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == imm)
              | .Cmp_NE => (element1 != imm)
              | .Cmp_GE => (element1 ≥b imm)
              | .Cmp_LT => (element1 <b imm)
              | .Cmp_GT => (element1 >b imm)
              | .Cmp_LE => (element1 ≤b imm)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPGE_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == imm)
              | .Cmp_NE => (element1 != imm)
              | .Cmp_GE => (element1 ≥b imm)
              | .Cmp_LT => (element1 <b imm)
              | .Cmp_GT => (element1 >b imm)
              | .Cmp_LE => (element1 ≤b imm)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPGT_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == imm)
              | .Cmp_NE => (element1 != imm)
              | .Cmp_GE => (element1 ≥b imm)
              | .Cmp_LT => (element1 <b imm)
              | .Cmp_GT => (element1 >b imm)
              | .Cmp_LE => (element1 ≤b imm)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPLT_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == imm)
              | .Cmp_NE => (element1 != imm)
              | .Cmp_GE => (element1 ≥b imm)
              | .Cmp_LT => (element1 <b imm)
              | .Cmp_GT => (element1 >b imm)
              | .Cmp_LE => (element1 ≤b imm)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPLE_P_P_ZI__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
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
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == imm)
              | .Cmp_NE => (element1 != imm)
              | .Cmp_GE => (element1 ≥b imm)
              | .Cmp_LT => (element1 <b imm)
              | .Cmp_GT => (element1 >b imm)
              | .Cmp_LE => (element1 ≤b imm)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPEQ_P_P_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 (Int.ediv (e *i esize) 64) 64)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPNE_P_P_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 (Int.ediv (e *i esize) 64) 64)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPHS_P_P_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 (Int.ediv (e *i esize) 64) 64)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPHI_P_P_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 (Int.ediv (e *i esize) 64) 64)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPLO_P_P_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 (Int.ediv (e *i esize) 64) 64)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPLS_P_P_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 (Int.ediv (e *i esize) 64) 64)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPGE_P_P_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 (Int.ediv (e *i esize) 64) 64)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPGT_P_P_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 (Int.ediv (e *i esize) 64) 64)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPLT_P_P_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 (Int.ediv (e *i esize) 64) 64)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPLE_P_P_ZW__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 (Int.ediv (e *i esize) 64) 64)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPEQ_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPNE_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPGE_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPGT_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPHS_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_CMPHI_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let cond ← (( do (undefined_bool ()) ) : SailM Bool )
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let cond : Bool :=
              match op with
              | .Cmp_EQ => (element1 == element2)
              | .Cmp_NE => (element1 != element2)
              | .Cmp_GE => (element1 ≥b element2)
              | .Cmp_LT => (element1 <b element2)
              | .Cmp_GT => (element1 >b element2)
              | .Cmp_LE => (element1 ≤b element2)
              | _ => cond
            let pbit : (BitVec 1) :=
              if (cond : Bool)
              then 1#1
              else 0#1
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize)))
        else (do (Elem_set result e psize (Sail.BitVec.zeroExtend 0#1 psize)))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let split_vec ← do (PredTest mask result esize)
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECP_R_P_R__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  (X_set dn 64 (BitVec.subInt operand1 count))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCP_R_P_R__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  (X_set dn 64 (BitVec.addInt operand1 count))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize = 32 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCP_R_P_R_UW (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let element ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element +i count) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize = 32 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCP_R_P_R_SX (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let element ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element +i count) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize = 64 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCP_R_P_R_X (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let element ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element +i count) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize = 64 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCP_R_P_R_X (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let element ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element +i count) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize = 32 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECP_R_P_R_UW (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let element ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element -i count) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize = 32 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECP_R_P_R_SX (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let element ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element -i count) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize = 64 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECP_R_P_R_X (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let element ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element -i count) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, ssize : Nat, ssize = 64 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECP_R_P_R_X (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let element ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element -i count) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars_1 := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do (Elem_set result e esize (BitVec.subInt (← (Elem_read operand1 e esize)) count))
    (pure loop_vars_1) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars_1 := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do (Elem_set result e esize (BitVec.addInt (← (Elem_read operand1 e esize)) count))
    (pure loop_vars_1) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars_1 := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do
        let element ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element +i count) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars_1) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars_1 := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do
        let element ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element +i count) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars_1) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars_1 := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do
        let element ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element -i count) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars_1) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := count
    for e in [loop_e_lower:loop_e_upper:1]i do
      let count := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement operand2 e esize)) : Bool)
        then (pure (count +i 1))
        else (pure count)
    (pure loop_vars) ) : SailM Int )
  let count := count
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars_1 := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do
        let element ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let (__tup_0, _) ← do (SatQ (element -i count) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars_1) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECB_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let VL := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.subInt operand1 (count *i imm)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECH_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let VL := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.subInt operand1 (count *i imm)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECW_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let VL := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.subInt operand1 (count *i imm)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECD_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let VL := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.subInt operand1 (count *i imm)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCB_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let VL := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.addInt operand1 (count *i imm)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCH_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let VL := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.addInt operand1 (count *i imm)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCW_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let VL := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.addInt operand1 (count *i imm)))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCD_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let VL := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.addInt operand1 (count *i imm)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCB_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCH_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCW_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCD_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCB_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCH_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCW_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCD_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCB_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCH_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCW_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCD_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCB_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCH_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCW_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCD_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECB_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECH_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECW_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECD_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECB_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECH_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECW_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECD_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECB_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECH_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECW_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECD_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECB_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECH_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECW_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize = 64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECD_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (X_read dn ssize) ) : SailM (BitVec ssize) )
  let result ← (( do (undefined_bitvector ssize) ) : SailM (BitVec ssize) )
  let element1 ← do (asl_Int operand1 is_unsigned)
  let result ← (( do
    let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) ssize is_unsigned)
    (pure __tup_0) ) : SailM (BitVec ssize) )
  (X_set dn 64 (← (Extend result 64 is_unsigned)))

/-- Type quantifiers: d : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_CNTB_R_S__ (d : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  (X_set d 64 (integer_subrange (count *i imm) 63 0))

/-- Type quantifiers: d : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_CNTH_R_S__ (d : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  (X_set d 64 (integer_subrange (count *i imm) 63 0))

/-- Type quantifiers: d : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_CNTW_R_S__ (d : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  (X_set d 64 (integer_subrange (count *i imm) 63 0))

/-- Type quantifiers: d : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_CNTD_R_S__ (d : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← do (DecodePredCount pat esize)
  (X_set d 64 (integer_subrange (count *i imm) 63 0))

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (BitVec.subInt (← (Elem_read operand1 e esize)) (count *i imm)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (BitVec.subInt (← (Elem_read operand1 e esize)) (count *i imm)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (BitVec.subInt (← (Elem_read operand1 e esize)) (count *i imm)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (BitVec.addInt (← (Elem_read operand1 e esize)) (count *i imm)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (BitVec.addInt (← (Elem_read operand1 e esize)) (count *i imm)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (BitVec.addInt (← (Elem_read operand1 e esize)) (count *i imm)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 +i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let count ← do (DecodePredCount pat esize)
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
        let (__tup_0, _) ← do (SatQ (element1 -i (count *i imm)) esize is_unsigned)
        (Elem_set result e esize __tup_0)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] -/
def execute_CTERMEQ_RR__ (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
  let operand1 ← (( do (X_read n esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (X_read m esize) ) : SailM (BitVec esize) )
  let element1 := (BitVec.toNat operand1)
  let element2 := (BitVec.toNat operand2)
  let term ← (( do (undefined_bool ()) ) : SailM Bool )
  let term : Bool :=
    match op with
    | .Cmp_EQ => (element1 == element2)
    | .Cmp_NE => (element1 != element2)
    | _ => term
  if (term : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := 1#1 }
      writeReg PSTATE { (← readReg PSTATE) with V := 0#1 })
  else
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := 0#1 }
      writeReg PSTATE { (← readReg PSTATE) with V := ← (do (pure (Complement.complement (← readReg PSTATE).C))) })

/-- Type quantifiers: esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] -/
def execute_CTERMNE_RR__ (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
  let operand1 ← (( do (X_read n esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (X_read m esize) ) : SailM (BitVec esize) )
  let element1 := (BitVec.toNat operand1)
  let element2 := (BitVec.toNat operand2)
  let term ← (( do (undefined_bool ()) ) : SailM Bool )
  let term : Bool :=
    match op with
    | .Cmp_EQ => (element1 == element2)
    | .Cmp_NE => (element1 != element2)
    | _ => term
  if (term : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := 1#1 }
      writeReg PSTATE { (← readReg PSTATE) with V := 0#1 })
  else
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := 0#1 }
      writeReg PSTATE { (← readReg PSTATE) with V := ← (do (pure (Complement.complement (← readReg PSTATE).C))) })

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FDUP_Z_I__ (VL : Nat) (d : Nat) (esize : Nat) (imm : (BitVec esize)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize imm)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, 0 ≤ g ∧ g ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCPY_Z_P_I__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : (BitVec esize)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize imm))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Int, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_DUP_Z_I__ (VL : Nat) (d : Nat) (esize : Nat) (imm : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let result : (BitVec VL) := (Replicate__1 (n := VL) (integer_subrange imm (esize -i 1) 0))
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_merging : Bool, 0 ≤ g ∧ g ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CPY_Z_P_I__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (merging : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let dest ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (integer_subrange imm (esize -i 1) 0)))
        else
          (do
            if (merging : Bool)
            then (do (Elem_set result e esize (← (Elem_read dest e esize))))
            else (do (Elem_set result e esize (Zeros (n := esize)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, imm : Int, k_merging : Bool, 0 ≤ g ∧ g ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CPY_Z_O_I__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (imm : Int) (merging : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let dest ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (integer_subrange imm (esize -i 1) 0)))
        else
          (do
            if (merging : Bool)
            then (do (Elem_set result e esize (← (Elem_read dest e esize))))
            else (do (Elem_set result e esize (Zeros (n := esize)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_DUPM_Z_I__ (VL : Nat) (d : Nat) (esize : Nat) (imm : (BitVec esize)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let result : (BitVec VL) := (BitVec.replicateBits imm (Int.ediv VL esize))
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 8 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UXTB_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            (Elem_set result e esize (← (Extend (Sail.BitVec.extractLsb element (s_esize -i 1) 0) esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UXTH_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            sail_assert ((0 ≤b (s_esize -i 1)) && ((s_esize -i 1) <b esize)) "src/instrs64_sve.sail:23846.74-23846.75"
            (Elem_set result e esize (← (Extend (Sail.BitVec.extractLsb element (s_esize -i 1) 0) esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UXTW_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            sail_assert ((0 ≤b (s_esize -i 1)) && ((s_esize -i 1) <b esize)) "src/instrs64_sve.sail:23921.74-23921.75"
            (Elem_set result e esize (← (Extend (Sail.BitVec.extractLsb element (s_esize -i 1) 0) esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 8 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SXTB_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            (Elem_set result e esize (← (Extend (Sail.BitVec.extractLsb element (s_esize -i 1) 0) esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 16 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SXTH_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            sail_assert ((0 ≤b (s_esize -i 1)) && ((s_esize -i 1) <b esize)) "src/instrs64_sve.sail:24064.74-24064.75"
            (Elem_set result e esize (← (Extend (Sail.BitVec.extractLsb element (s_esize -i 1) 0) esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, s_esize : Nat, s_esize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SXTW_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            sail_assert ((0 ≤b (s_esize -i 1)) && ((s_esize -i 1) <b esize)) "src/instrs64_sve.sail:24139.74-24139.75"
            (Elem_set result e esize (← (Extend (Sail.BitVec.extractLsb element (s_esize -i 1) 0) esize is_unsigned))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ANDV_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec esize) := (Ones (n := esize))
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (pure (result &&& (← (Elem_read operand e esize)))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec esize) )
  (V_set d esize result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_EORV_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec esize) := (Zeros (n := esize))
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (pure (result ^^^ (← (Elem_read operand e esize)))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec esize) )
  (V_set d esize result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ORV_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec esize) := (Zeros (n := esize))
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (pure (result ||| (← (Elem_read operand e esize)))))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec esize) )
  (V_set d esize result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SADDV_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let sum : Int := 0
  let sum ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := sum
    for e in [loop_e_lower:loop_e_upper:1]i do
      let sum := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand e esize))))
            (pure (sum +i element)))
        else (pure sum)
    (pure loop_vars) ) : SailM Int )
  let sum := sum
  (V_set d 64 (integer_subrange sum 63 0))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UADDV_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let sum : Int := 0
  let sum ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := sum
    for e in [loop_e_lower:loop_e_upper:1]i do
      let sum := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (pure (BitVec.toNat (← (Elem_read operand e esize))))
            (pure (sum +i element)))
        else (pure sum)
    (pure loop_vars) ) : SailM Int )
  let sum := sum
  (V_set d 64 (integer_subrange sum 63 0))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMAXV_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let maximum : Int :=
    if (is_unsigned : Bool)
    then 0
    else (Neg.neg (2 ^i (esize -i 1)))
  let maximum ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := maximum
    for e in [loop_e_lower:loop_e_upper:1]i do
      let maximum := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (asl_Int (← (Elem_read operand e esize)) is_unsigned)
            (pure (Max.max maximum element)))
        else (pure maximum)
    (pure loop_vars) ) : SailM Int )
  let maximum := maximum
  (V_set d esize (integer_subrange maximum (esize -i 1) 0))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMAXV_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let maximum : Int :=
    if (is_unsigned : Bool)
    then 0
    else (Neg.neg (2 ^i (esize -i 1)))
  let maximum ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := maximum
    for e in [loop_e_lower:loop_e_upper:1]i do
      let maximum := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (asl_Int (← (Elem_read operand e esize)) is_unsigned)
            (pure (Max.max maximum element)))
        else (pure maximum)
    (pure loop_vars) ) : SailM Int )
  let maximum := maximum
  (V_set d esize (integer_subrange maximum (esize -i 1) 0))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMINV_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let minimum : Int :=
    if (is_unsigned : Bool)
    then ((2 ^i esize) -i 1)
    else ((2 ^i (esize -i 1)) -i 1)
  let minimum ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := minimum
    for e in [loop_e_lower:loop_e_upper:1]i do
      let minimum := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (asl_Int (← (Elem_read operand e esize)) is_unsigned)
            (pure (Min.min minimum element)))
        else (pure minimum)
    (pure loop_vars) ) : SailM Int )
  let minimum := minimum
  (V_set d esize (integer_subrange minimum (esize -i 1) 0))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMINV_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let minimum : Int :=
    if (is_unsigned : Bool)
    then ((2 ^i esize) -i 1)
    else ((2 ^i (esize -i 1)) -i 1)
  let minimum ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := minimum
    for e in [loop_e_lower:loop_e_upper:1]i do
      let minimum := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then
          (do
            let element ← do (asl_Int (← (Elem_read operand e esize)) is_unsigned)
            (pure (Min.min minimum element)))
        else (pure minimum)
    (pure loop_vars) ) : SailM Int )
  let minimum := minimum
  (V_set d esize (integer_subrange minimum (esize -i 1) 0))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm1 : Int, imm2 : Int, List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_INDEX_Z_II__ (VL : Nat) (d : Nat) (esize : Nat) (imm1 : Int) (imm2 : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let index := (imm1 +i (e *i imm2))
        (Elem_set result e esize (integer_subrange index (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Int, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_INDEX_Z_IR__ (VL : Nat) (d : Nat) (esize : Nat) (imm : Int) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand2 ← (( do (X_read m esize) ) : SailM (BitVec esize) )
  let element2 := (BitVec.toInt operand2)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let index := (imm +i (e *i element2))
        (Elem_set result e esize (integer_subrange index (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_INDEX_Z_RI__ (VL : Nat) (d : Nat) (esize : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read n esize) ) : SailM (BitVec esize) )
  let element1 := (BitVec.toInt operand1)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let index := (element1 +i (e *i imm))
        (Elem_set result e esize (integer_subrange index (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_INDEX_Z_RR__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (X_read n esize) ) : SailM (BitVec esize) )
  let element1 := (BitVec.toInt operand1)
  let operand2 ← (( do (X_read m esize) ) : SailM (BitVec esize) )
  let element2 := (BitVec.toInt operand2)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let index := (element1 +i (e *i element2))
        (Elem_set result e esize (integer_subrange index (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_AND_Z_ZI__ (VL : Nat) (dn : Nat) (imm : (BitVec 64)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 64)
  let operand ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand e 64) ) : SailM (BitVec 64) )
        (Elem_set result e 64 (element1 &&& imm))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_EOR_Z_ZI__ (VL : Nat) (dn : Nat) (imm : (BitVec 64)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 64)
  let operand ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand e 64) ) : SailM (BitVec 64) )
        (Elem_set result e 64 (element1 ^^^ imm))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ORR_Z_ZI__ (VL : Nat) (dn : Nat) (imm : (BitVec 64)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 64)
  let operand ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand e 64) ) : SailM (BitVec 64) )
        (Elem_set result e 64 (element1 ||| imm))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_sub_op : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_MAD_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (sub_op : Bool) : SailM Unit := do
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
  let operand3 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read a VL)
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
            let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
            let product := (element1 *i element2)
            if (sub_op : Bool)
            then (do (Elem_set result e esize (BitVec.subInt (← (Elem_read operand3 e esize)) product)))
            else (do (Elem_set result e esize (BitVec.addInt (← (Elem_read operand3 e esize)) product))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_sub_op : Bool, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_MSB_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (sub_op : Bool) : SailM Unit := do
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
  let operand3 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read a VL)
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
            let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
            let product := (element1 *i element2)
            if (sub_op : Bool)
            then (do (Elem_set result e esize (BitVec.subInt (← (Elem_read operand3 e esize)) product)))
            else (do (Elem_set result e esize (BitVec.addInt (← (Elem_read operand3 e esize)) product))))
        else (do (Elem_set result e esize (← (Elem_read operand1 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_MLA_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
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
            let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
            let product := (element1 *i element2)
            if (sub_op : Bool)
            then (do (Elem_set result e esize (BitVec.subInt (← (Elem_read operand3 e esize)) product)))
            else (do (Elem_set result e esize (BitVec.addInt (← (Elem_read operand3 e esize)) product))))
        else (do (Elem_set result e esize (← (Elem_read operand3 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_MLS_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
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
  let operand3 ← (( do (Z_read da VL) ) : SailM (BitVec VL) )
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
            let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
            let product := (element1 *i element2)
            if (sub_op : Bool)
            then (do (Elem_set result e esize (BitVec.subInt (← (Elem_read operand3 e esize)) product)))
            else (do (Elem_set result e esize (BitVec.addInt (← (Elem_read operand3 e esize)) product))))
        else (do (Elem_set result e esize (← (Elem_read operand3 e esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set da VL result)

/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVPRFX_Z_Z__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let result ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_merging : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVPRFX_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (merging : Bool) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let dest ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
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
            let element ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            (Elem_set result e esize element))
        else
          (do
            if (merging : Bool)
            then (do (Elem_set result e esize (← (Elem_read dest e esize))))
            else (do (Elem_set result e esize (Zeros (n := esize)))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CNTP_R_P_P__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let sum : (BitVec 64) := (Zeros (n := 64))
  let sum ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := sum
    for e in [loop_e_lower:loop_e_upper:1]i do
      let sum := loop_vars
      loop_vars ← do
        if ((←((ActivePredicateElement mask e esize) <&&> (do
             (ActivePredicateElement operand e esize)))) : Bool)
        then (pure (BitVec.addInt sum 1))
        else (pure sum)
    (pure loop_vars) ) : SailM (BitVec 64) )
  (X_set d 64 sum)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_REV_P_P__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let result ← (( do (Reverse operand (Int.ediv esize 8)) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_TRN1_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) (Int.ediv esize 8) (← (Elem_read operand1 ((2 *i p) +i part) (Int.ediv esize 8))))
        (Elem_set result ((2 *i p) +i 1) (Int.ediv esize 8) (← (Elem_read operand2 ((2 *i p) +i part) (Int.ediv esize 8))))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_TRN2_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) (Int.ediv esize 8) (← (Elem_read operand1 ((2 *i p) +i part) (Int.ediv esize 8))))
        (Elem_set result ((2 *i p) +i 1) (Int.ediv esize 8) (← (Elem_read operand2 ((2 *i p) +i part) (Int.ediv esize 8))))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_UZP1_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result p (Int.ediv esize 8) (← (Elem_read operand1 ((2 *i p) +i part) (Int.ediv esize 8))))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars_1 := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do (Elem_set result (pairs +i p) (Int.ediv esize 8) (← (Elem_read operand2 ((2 *i p) +i part) (Int.ediv esize 8))))
    (pure loop_vars_1) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_UZP2_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result p (Int.ediv esize 8) (← (Elem_read operand1 ((2 *i p) +i part) (Int.ediv esize 8))))
    (pure loop_vars) ) : SailM (BitVec PL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars_1 := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do (Elem_set result (pairs +i p) (Int.ediv esize 8) (← (Elem_read operand2 ((2 *i p) +i part) (Int.ediv esize 8))))
    (pure loop_vars_1) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_ZIP1_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let base := (part *i pairs)
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) (Int.ediv esize 8) (← (Elem_read operand1 (base +i p) (Int.ediv esize 8))))
        (Elem_set result ((2 *i p) +i 1) (Int.ediv esize 8) (← (Elem_read operand2 (base +i p) (Int.ediv esize 8))))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_ZIP2_P_PP__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let operand2 ← (( do (P_read m PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let base := (part *i pairs)
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) (Int.ediv esize 8) (← (Elem_read operand1 (base +i p) (Int.ediv esize 8))))
        (Elem_set result ((2 *i p) +i 1) (Int.ediv esize 8) (← (Elem_read operand2 (base +i p) (Int.ediv esize 8))))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_REV_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (Reverse operand esize) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, k_double_table : Bool, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TBL_Z_ZZ_1 (VL : Nat) (d : Nat) (double_table : Bool) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let indexes ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let table_size :=
    if (double_table : Bool)
    then (VL *i 2)
    else VL
  let table_elems := (Int.ediv table_size esize)
  let table ← (( do (undefined_bitvector table_size) ) : SailM (BitVec table_size) )
  let table ← (( do
    if (double_table : Bool)
    then
      (do
        let top ← (( do (Z_read (Nat.mod (n +i 1) 32) VL) ) : SailM (BitVec VL) )
        let bottom ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
        (pure (Sail.BitVec.extractLsb (top +++ bottom) (table_size -i 1) 0)))
    else (do (Z_read n table_size)) ) : SailM (BitVec table_size) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let idx ← do (pure (BitVec.toNat (← (Elem_read indexes e esize))))
        (Elem_set result e esize
          (← (do
            if ((idx <b table_elems) : Bool)
            then (Elem_read table idx esize)
            else (pure (Zeros (n := esize))))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, k_double_table : Bool, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TBL_Z_ZZ_2 (VL : Nat) (d : Nat) (double_table : Bool) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let indexes ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let table_size :=
    if (double_table : Bool)
    then (VL *i 2)
    else VL
  let table_elems := (Int.ediv table_size esize)
  let table ← (( do (undefined_bitvector table_size) ) : SailM (BitVec table_size) )
  let table ← (( do
    if (double_table : Bool)
    then
      (do
        let top ← (( do (Z_read (Nat.mod (n +i 1) 32) VL) ) : SailM (BitVec VL) )
        let bottom ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
        (pure (Sail.BitVec.extractLsb (top +++ bottom) (table_size -i 1) 0)))
    else (do (Z_read n table_size)) ) : SailM (BitVec table_size) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let idx ← do (pure (BitVec.toNat (← (Elem_read indexes e esize))))
        (Elem_set result e esize
          (← (do
            if ((idx <b table_elems) : Bool)
            then (Elem_read table idx esize)
            else (pure (Zeros (n := esize))))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TRN1_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand1 ((2 *i p) +i part) esize)))
        (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand2 ((2 *i p) +i part) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TRN2_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand1 ((2 *i p) +i part) esize)))
        (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand2 ((2 *i p) +i part) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP1_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result p esize (← (Elem_read operand1 ((2 *i p) +i part) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars_1 := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do (Elem_set result (pairs +i p) esize (← (Elem_read operand2 ((2 *i p) +i part) esize)))
    (pure loop_vars_1) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP2_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result p esize (← (Elem_read operand1 ((2 *i p) +i part) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars_1 := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do (Elem_set result (pairs +i p) esize (← (Elem_read operand2 ((2 *i p) +i part) esize)))
    (pure loop_vars_1) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP1_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let base := (part *i pairs)
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand1 (base +i p) esize)))
        (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand2 (base +i p) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP2_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let base := (part *i pairs)
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand1 (base +i p) esize)))
        (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand2 (base +i p) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TRN1_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand1 ((2 *i p) +i part) esize)))
        (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand2 ((2 *i p) +i part) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TRN2_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand1 ((2 *i p) +i part) esize)))
        (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand2 ((2 *i p) +i part) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP1_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let base := (part *i pairs)
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand1 (base +i p) esize)))
        (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand2 (base +i p) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP2_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let base := (part *i pairs)
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand1 (base +i p) esize)))
        (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand2 (base +i p) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP1_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result p esize (← (Elem_read operand1 ((2 *i p) +i part) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars_1 := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do (Elem_set result (pairs +i p) esize (← (Elem_read operand2 ((2 *i p) +i part) esize)))
    (pure loop_vars_1) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP2_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pairs := (Int.ediv VL (esize *i 2))
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result p esize (← (Elem_read operand1 ((2 *i p) +i part) esize)))
    (pure loop_vars) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars_1 := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars_1
      loop_vars_1 ← do (Elem_set result (pairs +i p) esize (← (Elem_read operand2 ((2 *i p) +i part) esize)))
    (pure loop_vars_1) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, csize : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ List.elem csize [32, 64] ∧ (is_VL VL) -/
def execute_CLASTA_R_P_Z__ (VL : Nat) (csize : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (X_read dn esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector csize) ) : SailM (BitVec csize) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then
      (do
        sail_assert ((esize ≥b 0) && (csize ≥b esize)) "src/instrs64_sve.sail:27154.59-27154.60"
        (pure (Sail.BitVec.zeroExtend operand1 csize)))
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last := last
        sail_assert ((esize ≥b 0) && (csize ≥b esize)) "src/instrs64_sve.sail:27165.59-27165.60"
        (pure (Sail.BitVec.zeroExtend (← (Elem_read operand2 last esize)) csize))) ) : SailM (BitVec csize) )
  (X_set dn csize result)

/-- Type quantifiers: VL : Nat, csize : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ List.elem csize [32, 64] ∧ (is_VL VL) -/
def execute_CLASTB_R_P_Z__ (VL : Nat) (csize : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (X_read dn esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector csize) ) : SailM (BitVec csize) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then
      (do
        sail_assert ((esize ≥b 0) && (csize ≥b esize)) "src/instrs64_sve.sail:27229.59-27229.60"
        (pure (Sail.BitVec.zeroExtend operand1 csize)))
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last := last
        sail_assert ((esize ≥b 0) && (csize ≥b esize)) "src/instrs64_sve.sail:27240.59-27240.60"
        (pure (Sail.BitVec.zeroExtend (← (Elem_read operand2 last esize)) csize))) ) : SailM (BitVec csize) )
  (X_set dn csize result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_CLASTA_V_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (V_read dn esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then (pure (Sail.BitVec.zeroExtend operand1 esize))
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last := last
        (Elem_read operand2 last esize)) ) : SailM (BitVec esize) )
  (V_set dn esize result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_CLASTB_V_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (V_read dn esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then (pure (Sail.BitVec.zeroExtend operand1 esize))
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last := last
        (Elem_read operand2 last esize)) ) : SailM (BitVec esize) )
  (V_set dn esize result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_CLASTA_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then (pure operand1)
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last := last
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars
          loop_vars ← do (Elem_set result e esize (← (Elem_read operand2 last esize)))
        (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_CLASTB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read dn VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then (pure operand1)
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last := last
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars
          loop_vars ← do (Elem_set result e esize (← (Elem_read operand2 last esize)))
        (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_COMPACT_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read n VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Zeros (n := VL))
  let x : Int := 0
  let (result, x) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (result, x)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (result, x) := loop_vars
      loop_vars ← do
        let (result, x) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let element ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let result ← (( do
                let x := x
                (Elem_set result x esize element) ) : SailM (BitVec VL) )
              let x : Int := (x +i 1)
              (pure (result, x)))
          else (pure (result, x)) ) : SailM ((BitVec VL) × Int) )
        (pure (result, x))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, dst : Nat, esize : Nat, s1 : Nat, s2 : Nat, v : Nat, List.elem v [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ s2 ∧ s2 ≤ 31 ∧ 0 ≤ s1 ∧ s1 ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dst ∧ dst ≤ 31 ∧ (is_VL VL) -/
def execute_SPLICE_Z_P_ZZ_Des (VL : Nat) (dst : Nat) (esize : Nat) (s1 : Nat) (s2 : Nat) (v : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read v PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read s1 VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read s2 VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let x : Int := 0
  let active : Bool := false
  let lastnum ← do (LastActiveElement mask esize)
  let (result, x) ← (( do
    if ((lastnum ≥b 0) : Bool)
    then
      (do
        let (active, result, x) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := lastnum
          let mut loop_vars := (active, result, x)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (active, result, x) := loop_vars
            loop_vars ← do
              let active ← (pure active) <||> (do (ActivePredicateElement mask e esize))
              let (result, x) ← (( do
                if (active : Bool)
                then
                  (do
                    let result ← (( do
                      let x := x
                      (Elem_set result x esize (← (Elem_read operand1 e esize))) ) : SailM (BitVec VL) )
                    let x : Int := (x +i 1)
                    (pure (result, x)))
                else (pure (result, x)) ) : SailM ((BitVec VL) × Int) )
              (pure (active, result, x))
          (pure loop_vars) ) : SailM (Bool × (BitVec VL) × Int) )
        (pure (result, x)))
    else (pure (result, x)) ) : SailM ((BitVec VL) × Int) )
  let nelements := ((elements -i x) -i 1)
  let (result, x) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := nelements
    let mut loop_vars_1 := (result, x)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (result, x) := loop_vars_1
      loop_vars_1 ← do
        let result ← (( do
          let x := x
          (Elem_set result x esize (← (Elem_read operand2 e esize))) ) : SailM (BitVec VL) )
        let x : Int := (x +i 1)
        (pure (result, x))
    (pure loop_vars_1) ) : SailM ((BitVec VL) × Int) )
  (Z_set dst VL result)

/-- Type quantifiers: VL : Nat, dst : Nat, esize : Nat, s1 : Nat, s2 : Int, v : Nat, List.elem v [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ s1 ∧ s1 ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dst ∧ dst ≤ 31 ∧ (is_VL VL) -/
def execute_SPLICE_Z_P_ZZ_Con (VL : Nat) (dst : Nat) (esize : Nat) (s1 : Nat) (s2 : Int) (v : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read v PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (Z_read s1 VL)
    else (pure (Zeros (n := VL))) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read s2 VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let x : Int := 0
  let active : Bool := false
  let lastnum ← do (LastActiveElement mask esize)
  let (result, x) ← (( do
    if ((lastnum ≥b 0) : Bool)
    then
      (do
        let (active, result, x) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := lastnum
          let mut loop_vars := (active, result, x)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (active, result, x) := loop_vars
            loop_vars ← do
              let active ← (pure active) <||> (do (ActivePredicateElement mask e esize))
              let (result, x) ← (( do
                if (active : Bool)
                then
                  (do
                    let result ← (( do
                      let x := x
                      (Elem_set result x esize (← (Elem_read operand1 e esize))) ) : SailM (BitVec VL) )
                    let x : Int := (x +i 1)
                    (pure (result, x)))
                else (pure (result, x)) ) : SailM ((BitVec VL) × Int) )
              (pure (active, result, x))
          (pure loop_vars) ) : SailM (Bool × (BitVec VL) × Int) )
        (pure (result, x)))
    else (pure (result, x)) ) : SailM ((BitVec VL) × Int) )
  let nelements := ((elements -i x) -i 1)
  let (result, x) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := nelements
    let mut loop_vars_1 := (result, x)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (result, x) := loop_vars_1
      loop_vars_1 ← do
        let result ← (( do
          let x := x
          (Elem_set result x esize (← (Elem_read operand2 e esize))) ) : SailM (BitVec VL) )
        let x : Int := (x +i 1)
        (pure (result, x))
    (pure loop_vars_1) ) : SailM ((BitVec VL) × Int) )
  (Z_set dst VL result)

/-- Type quantifiers: VL : Nat, dst : Nat, esize : Nat, position__arg : Nat, s1 : Nat, s2 : Nat, 0 ≤ s2 ∧ s2 ≤ 31 ∧ 0 ≤ s1 ∧ s1 ≤ 31 ∧ 0 ≤ position__arg ∧ position__arg ≤ 255 ∧ esize = 8 ∧ 0 ≤ dst ∧ dst ≤ 31 ∧ (is_VL VL) -/
def execute_EXT_Z_ZI_Des (VL : Nat) (dst : Nat) (esize : Nat) (position__arg : Nat) (s1 : Nat) (s2 : Nat) : SailM Unit := do
  let position : Int := position__arg
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read s1 VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read s2 VL) ) : SailM (BitVec VL) )
  let position : Int :=
    if ((position ≥b elements) : Bool)
    then 0
    else position
  let position := (Int.shiftl position 3)
  let concat : (BitVec (VL * 2)) := (operand2 +++ operand1)
  sail_assert ((0 ≤b position) && (((position +i VL) -i 1) <b (VL *i 2))) "src/instrs64_sve.sail:27842.71-27842.72"
  let result : (BitVec VL) := (Sail.BitVec.extractLsb concat ((position +i VL) -i 1) position)
  (Z_set dst VL result)

/-- Type quantifiers: VL : Nat, dst : Nat, esize : Nat, position__arg : Nat, s1 : Nat, s2 : Int, 0 ≤ s1 ∧ s1 ≤ 31 ∧ 0 ≤ position__arg ∧ position__arg ≤ 255 ∧ esize = 8 ∧ 0 ≤ dst ∧ dst ≤ 31 ∧ (is_VL VL) -/
def execute_EXT_Z_ZI_Con (VL : Nat) (dst : Nat) (esize : Nat) (position__arg : Nat) (s1 : Nat) (s2 : Int) : SailM Unit := do
  let position : Int := position__arg
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read s1 VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read s2 VL) ) : SailM (BitVec VL) )
  let position : Int :=
    if ((position ≥b elements) : Bool)
    then 0
    else position
  let position := (Int.shiftl position 3)
  let concat : (BitVec (VL * 2)) := (operand2 +++ operand1)
  sail_assert ((0 ≤b position) && (((position +i VL) -i 1) <b (VL *i 2))) "src/instrs64_sve.sail:27905.71-27905.72"
  let result : (BitVec VL) := (Sail.BitVec.extractLsb concat ((position +i VL) -i 1) position)
  (Z_set dst VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CPY_Z_P_R__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let operand1 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
        let operand1 ← (( do
          if ((n == 31) : Bool)
          then (do (SP_read ()))
          else (do (X_read n 64)) ) : SailM (BitVec 64) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars
          loop_vars ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then (do (Elem_set result e esize (Sail.BitVec.extractLsb operand1 (esize -i 1) 0)))
            else (pure result)
        (pure loop_vars))
    else (pure result) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CPY_Z_P_V__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (V_read n esize)
    else (pure (Zeros (n := esize))) ) : SailM (BitVec esize) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize operand1))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ index ∧ index ≤ 63 ∧ List.elem esize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_DUP_Z_Zi__ (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element ← (( do
    if ((index ≥b elements) : Bool)
    then (pure (Zeros (n := esize)))
    else (do (Elem_read operand1 index esize)) ) : SailM (BitVec esize) )
  let result : (BitVec VL) := (BitVec.replicateBits element (Int.ediv VL esize))
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_DUP_Z_R__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let PL := (Int.ediv VL 8)
  let operand ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let operand ← (( do
    if ((n == 31) : Bool)
    then (do (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (Sail.BitVec.extractLsb operand (esize -i 1) 0))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_isBefore : Bool, n : Nat, rsize : Nat, List.elem rsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LASTA_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (n : Nat) (rsize : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let last : Int :=
    if (isBefore : Bool)
    then
      (if ((last <b 0) : Bool)
      then (elements -i 1)
      else last)
    else
      (let last : Int := (last +i 1)
      if ((last ≥b elements) : Bool)
      then 0
      else last)
  let last := last
  sail_assert (rsize ≥b esize) "src/instrs64_sve.sail:28256.39-28256.40"
  let result ← (( do (pure (Sail.BitVec.zeroExtend (← (Elem_read operand last esize)) rsize)) ) : SailM (BitVec rsize) )
  (X_set d rsize result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_isBefore : Bool, n : Nat, rsize : Nat, List.elem rsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LASTB_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (n : Nat) (rsize : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let last : Int :=
    if (isBefore : Bool)
    then
      (if ((last <b 0) : Bool)
      then (elements -i 1)
      else last)
    else
      (let last : Int := (last +i 1)
      if ((last ≥b elements) : Bool)
      then 0
      else last)
  let last := last
  sail_assert (rsize ≥b esize) "src/instrs64_sve.sail:28329.39-28329.40"
  let result ← (( do (pure (Sail.BitVec.zeroExtend (← (Elem_read operand last esize)) rsize)) ) : SailM (BitVec rsize) )
  (X_set d rsize result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_isBefore : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LASTA_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let last : Int :=
    if (isBefore : Bool)
    then
      (if ((last <b 0) : Bool)
      then (elements -i 1)
      else last)
    else
      (let last : Int := (last +i 1)
      if ((last ≥b elements) : Bool)
      then 0
      else last)
  let last := last
  (V_set d esize (← (Elem_read operand last esize)))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_isBefore : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LASTB_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let last : Int :=
    if (isBefore : Bool)
    then
      (if ((last <b 0) : Bool)
      then (elements -i 1)
      else last)
    else
      (let last : Int := (last +i 1)
      if ((last ≥b elements) : Bool)
      then 0
      else last)
  let last := last
  (V_set d esize (← (Elem_read operand last esize)))

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PUNPKLO_P_P__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let pbit ← (( do
          (PredicateElement operand
            (if (hi : Bool)
            then (e +i elements)
            else e) (Int.ediv esize 2)) ) : SailM (BitVec 1) )
        (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PUNPKHI_P_P__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let operand ← (( do (P_read n PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let psize := (Int.ediv esize 8)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let pbit ← (( do
          (PredicateElement operand
            (if (hi : Bool)
            then (e +i elements)
            else e) (Int.ediv esize 2)) ) : SailM (BitVec 1) )
        (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
    (pure loop_vars) ) : SailM (BitVec PL) )
  (P_set d PL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, swsize : Nat, swsize = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_REVW_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (swsize : Nat) : SailM Unit := do
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


