import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
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

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPA_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := result
    for row in [loop_row_lower:loop_row_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 row esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 col esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
            if ((←((ActivePredicateElement mask1 row esize) <&&> (do
                 (ActivePredicateElement mask2 col esize)))) : Bool)
            then
              (do
                let element1 ← (( do
                  if (sub_op : Bool)
                  then (do (FPNeg element1))
                  else (pure element1) ) : SailM (BitVec esize) )
                (Elem_set result ((row *i dim) +i col) esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ()))))))
            else (do (Elem_set result ((row *i dim) +i col) esize element3))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := result
    for row in [loop_row_lower:loop_row_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 row esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 col esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
            if ((←((ActivePredicateElement mask1 row esize) <&&> (do
                 (ActivePredicateElement mask2 col esize)))) : Bool)
            then
              (do
                let element1 ← (( do
                  if (sub_op : Bool)
                  then (do (FPNeg element1))
                  else (pure element1) ) : SailM (BitVec esize) )
                (Elem_set result ((row *i dim) +i col) esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ()))))))
            else (do (Elem_set result ((row *i dim) +i col) esize element3))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPA_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := result
    for row in [loop_row_lower:loop_row_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 row esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 col esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
            if ((←((ActivePredicateElement mask1 row esize) <&&> (do
                 (ActivePredicateElement mask2 col esize)))) : Bool)
            then
              (do
                let element1 ← (( do
                  if (sub_op : Bool)
                  then (do (FPNeg element1))
                  else (pure element1) ) : SailM (BitVec esize) )
                (Elem_set result ((row *i dim) +i col) esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ()))))))
            else (do (Elem_set result ((row *i dim) +i col) esize element3))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPS_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := result
    for row in [loop_row_lower:loop_row_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 row esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 col esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
            if ((←((ActivePredicateElement mask1 row esize) <&&> (do
                 (ActivePredicateElement mask2 col esize)))) : Bool)
            then
              (do
                let element1 ← (( do
                  if (sub_op : Bool)
                  then (do (FPNeg element1))
                  else (pure element1) ) : SailM (BitVec esize) )
                (Elem_set result ((row *i dim) +i col) esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ()))))))
            else (do (Elem_set result ((row *i dim) +i col) esize element3))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_32 : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_32 = (VL / 32 * (VL / 32 * 32)) -/
def execute_BFMOPA_ZA32_PP_ZZ__ (VL : Nat) (dim_dim_32 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL 32)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da 32 dim_dim_32) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do (undefined_bitvector dim_dim_32) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := result
    for row in [loop_row_lower:loop_row_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let prow_0 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 0) 16) ) : SailM Bool )
            let prow_1 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 1) 16) ) : SailM Bool )
            let pcol_0 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 0) 16) ) : SailM Bool )
            let pcol_1 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 1) 16) ) : SailM Bool )
            let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) 32) ) : SailM (BitVec 32) )
            let sum ← (( do
              if (((prow_0 && pcol_0) || (prow_1 && pcol_1)) : Bool)
              then
                (do
                  let erow_0 ← (( do
                    if (prow_0 : Bool)
                    then (Elem_read operand1 ((2 *i row) +i 0) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let erow_1 ← (( do
                    if (prow_1 : Bool)
                    then (Elem_read operand1 ((2 *i row) +i 1) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let ecol_0 ← (( do
                    if (pcol_0 : Bool)
                    then (Elem_read operand2 ((2 *i col) +i 0) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let ecol_1 ← (( do
                    if (pcol_1 : Bool)
                    then (Elem_read operand2 ((2 *i col) +i 1) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let (erow_0, erow_1) ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        let honor_altfp : Bool := false
                        let erow_0 ← (( do
                          if (prow_0 : Bool)
                          then (do (BFNeg__1 erow_0 honor_altfp))
                          else (pure erow_0) ) : SailM (BitVec 16) )
                        let erow_1 ← (( do
                          if (prow_1 : Bool)
                          then (do (BFNeg__1 erow_1 honor_altfp))
                          else (pure erow_1) ) : SailM (BitVec 16) )
                        (pure (erow_0, erow_1)))
                    else (pure (erow_0, erow_1)) ) : SailM ((BitVec 16) × (BitVec 16)) )
                  (BFDotAdd sum erow_0 erow_1 ecol_0 ecol_1 (← (FPCR_read ()))))
              else (pure sum) ) : SailM (BitVec 32) )
            (Elem_set result ((row *i dim) +i col) 32 sum)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_32) )
  (ZAtile_set VL da 32 dim_dim_32 result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_32 : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_32 = (VL / 32 * (VL / 32 * 32)) -/
def execute_BFMOPS_ZA32_PP_ZZ__ (VL : Nat) (dim_dim_32 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL 32)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da 32 dim_dim_32) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do (undefined_bitvector dim_dim_32) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := result
    for row in [loop_row_lower:loop_row_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let prow_0 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 0) 16) ) : SailM Bool )
            let prow_1 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 1) 16) ) : SailM Bool )
            let pcol_0 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 0) 16) ) : SailM Bool )
            let pcol_1 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 1) 16) ) : SailM Bool )
            let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) 32) ) : SailM (BitVec 32) )
            let sum ← (( do
              if (((prow_0 && pcol_0) || (prow_1 && pcol_1)) : Bool)
              then
                (do
                  let erow_0 ← (( do
                    if (prow_0 : Bool)
                    then (Elem_read operand1 ((2 *i row) +i 0) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let erow_1 ← (( do
                    if (prow_1 : Bool)
                    then (Elem_read operand1 ((2 *i row) +i 1) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let ecol_0 ← (( do
                    if (pcol_0 : Bool)
                    then (Elem_read operand2 ((2 *i col) +i 0) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let ecol_1 ← (( do
                    if (pcol_1 : Bool)
                    then (Elem_read operand2 ((2 *i col) +i 1) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let (erow_0, erow_1) ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        let honor_altfp : Bool := false
                        let erow_0 ← (( do
                          if (prow_0 : Bool)
                          then (do (BFNeg__1 erow_0 honor_altfp))
                          else (pure erow_0) ) : SailM (BitVec 16) )
                        let erow_1 ← (( do
                          if (prow_1 : Bool)
                          then (do (BFNeg__1 erow_1 honor_altfp))
                          else (pure erow_1) ) : SailM (BitVec 16) )
                        (pure (erow_0, erow_1)))
                    else (pure (erow_0, erow_1)) ) : SailM ((BitVec 16) × (BitVec 16)) )
                  (BFDotAdd sum erow_0 erow_1 ecol_0 ecol_1 (← (FPCR_read ()))))
              else (pure sum) ) : SailM (BitVec 32) )
            (Elem_set result ((row *i dim) +i col) 32 sum)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_32) )
  (ZAtile_set VL da 32 dim_dim_32 result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_32 : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_32 = (VL / 32 * (VL / 32 * 32)) -/
def execute_FMOPA_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_32 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL 32)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da 32 dim_dim_32) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do (undefined_bitvector dim_dim_32) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := result
    for row in [loop_row_lower:loop_row_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let prow_0 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 0) 16) ) : SailM Bool )
            let prow_1 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 1) 16) ) : SailM Bool )
            let pcol_0 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 0) 16) ) : SailM Bool )
            let pcol_1 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 1) 16) ) : SailM Bool )
            let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) 32) ) : SailM (BitVec 32) )
            let sum ← (( do
              if (((prow_0 && pcol_0) || (prow_1 && pcol_1)) : Bool)
              then
                (do
                  let erow_0 ← (( do
                    if (prow_0 : Bool)
                    then (Elem_read operand1 ((2 *i row) +i 0) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let erow_1 ← (( do
                    if (prow_1 : Bool)
                    then (Elem_read operand1 ((2 *i row) +i 1) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let ecol_0 ← (( do
                    if (pcol_0 : Bool)
                    then (Elem_read operand2 ((2 *i col) +i 0) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let ecol_1 ← (( do
                    if (pcol_1 : Bool)
                    then (Elem_read operand2 ((2 *i col) +i 1) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let (erow_0, erow_1) ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        let erow_0 ← (( do
                          if (prow_0 : Bool)
                          then (do (FPNeg erow_0))
                          else (pure erow_0) ) : SailM (BitVec 16) )
                        let erow_1 ← (( do
                          if (prow_1 : Bool)
                          then (do (FPNeg erow_1))
                          else (pure erow_1) ) : SailM (BitVec 16) )
                        (pure (erow_0, erow_1)))
                    else (pure (erow_0, erow_1)) ) : SailM ((BitVec 16) × (BitVec 16)) )
                  (FPDotAdd_ZA sum erow_0 erow_1 ecol_0 ecol_1 (← (FPCR_read ()))))
              else (pure sum) ) : SailM (BitVec 32) )
            (Elem_set result ((row *i dim) +i col) 32 sum)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_32) )
  (ZAtile_set VL da 32 dim_dim_32 result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_32 : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_32 = (VL / 32 * (VL / 32 * 32)) -/
def execute_FMOPS_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_32 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL 32)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da 32 dim_dim_32) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do (undefined_bitvector dim_dim_32) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := result
    for row in [loop_row_lower:loop_row_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let prow_0 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 0) 16) ) : SailM Bool )
            let prow_1 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 1) 16) ) : SailM Bool )
            let pcol_0 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 0) 16) ) : SailM Bool )
            let pcol_1 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 1) 16) ) : SailM Bool )
            let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) 32) ) : SailM (BitVec 32) )
            let sum ← (( do
              if (((prow_0 && pcol_0) || (prow_1 && pcol_1)) : Bool)
              then
                (do
                  let erow_0 ← (( do
                    if (prow_0 : Bool)
                    then (Elem_read operand1 ((2 *i row) +i 0) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let erow_1 ← (( do
                    if (prow_1 : Bool)
                    then (Elem_read operand1 ((2 *i row) +i 1) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let ecol_0 ← (( do
                    if (pcol_0 : Bool)
                    then (Elem_read operand2 ((2 *i col) +i 0) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let ecol_1 ← (( do
                    if (pcol_1 : Bool)
                    then (Elem_read operand2 ((2 *i col) +i 1) 16)
                    else (FPZero 0#1 16) ) : SailM (BitVec 16) )
                  let (erow_0, erow_1) ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        let erow_0 ← (( do
                          if (prow_0 : Bool)
                          then (do (FPNeg erow_0))
                          else (pure erow_0) ) : SailM (BitVec 16) )
                        let erow_1 ← (( do
                          if (prow_1 : Bool)
                          then (do (FPNeg erow_1))
                          else (pure erow_1) ) : SailM (BitVec 16) )
                        (pure (erow_0, erow_1)))
                    else (pure (erow_0, erow_1)) ) : SailM ((BitVec 16) × (BitVec 16)) )
                  (FPDotAdd_ZA sum erow_0 erow_1 ecol_0 ecol_1 (← (FPCR_read ()))))
              else (pure sum) ) : SailM (BitVec 32) )
            (Elem_set result ((row *i dim) +i col) 32 sum)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_32) )
  (ZAtile_set VL da 32 dim_dim_32 result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPA_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SUMOPA_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_USMOPA_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPA_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SUMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_USMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPA_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SUMOPA_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_USMOPA_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPA_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPS_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SUMOPS_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_USMOPS_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPS_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := (prod, result)
    for row in [loop_row_lower:loop_row_upper:1]i do
      let (prod, result) := loop_vars
      loop_vars ← do
        let (prod, result) ← (( do
          let loop_col_lower := 0
          let loop_col_upper := (dim -i 1)
          let mut loop_vars_1 := (prod, result)
          for col in [loop_col_lower:loop_col_upper:1]i do
            let (prod, result) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 3
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4)) <&&> (do
                           (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((4 *i row) +i k) (Int.ediv esize 4))) op1_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((4 *i col) +i k) (Int.ediv esize 4))) op2_unsigned))))
                          let prod : Int :=
                            if (sub_op : Bool)
                            then (Neg.neg prod)
                            else prod
                          let sum : (BitVec esize) := (BitVec.addInt sum prod)
                          (pure (prod, sum)))
                      else (pure (prod, sum)) ) : SailM (Int × (BitVec esize)) )
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec esize)) )
              let result ← (Elem_set result ((row *i dim) +i col) esize sum)
              (pure (prod, result))
          (pure loop_vars_1) ) : SailM (Int × (BitVec dim_dim_esize)) )
        (pure (prod, result))
    (pure loop_vars) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ d = 0 ∧ (is_VL VL) -/
def execute_MOVA_ZA_P_RZ_B (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let result ← (( do (ZAslice_read d esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize element))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (ZAslice_set d esize vertical slice_name VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ List.elem d [0, 1] ∧ (is_VL VL) -/
def execute_MOVA_ZA_P_RZ_H (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let result ← (( do (ZAslice_read d esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize element))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (ZAslice_set d esize vertical slice_name VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ List.elem d [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_MOVA_ZA_P_RZ_W (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let result ← (( do (ZAslice_read d esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize element))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (ZAslice_set d esize vertical slice_name VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_MOVA_ZA_P_RZ_D (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let result ← (( do (ZAslice_read d esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize element))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (ZAslice_set d esize vertical slice_name VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_MOVA_ZA_P_RZ_Q (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let result ← (( do (ZAslice_read d esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize element))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (ZAslice_set d esize vertical slice_name VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ n = 0 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_Z_P_RZA_B (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let operand ← (( do (ZAslice_read n esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize element))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem n [0, 1] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_Z_P_RZA_H (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let operand ← (( do (ZAslice_read n esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize element))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3] ∧ List.elem n [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_Z_P_RZA_W (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let operand ← (( do (ZAslice_read n esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize element))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1] ∧ List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_Z_P_RZA_D (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let operand ← (( do (ZAslice_read n esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize element))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ 0 ≤ n ∧ n ≤ 15 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_Z_P_RZA_Q (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let operand ← (( do (ZAslice_read n esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let result ← (( do (Z_read d VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e esize) ) : SailM (BitVec esize) )
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize element))
        else (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: SVL : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL SVL) -/
def execute_LDR_ZA_RI__ (SVL : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckSMEAndZAEnabled ())
  let SVL := SVL
  let dim := (Int.ediv SVL 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let moffs : Int := (offset *i dim)
  let result ← (( do (undefined_bitvector SVL) ) : SailM (BitVec SVL) )
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec := (Nat.mod ((BitVec.toNat vbase) +i offset) dim)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSME MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  if ((←((HaveTME ()) <&&> (do
       (pure ((← readReg TSTATE).depth >b 0))))) : Bool)
  then (FailTransaction TMFailure_ERR false)
  else (pure ())
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base moffs) 16)
  if ((←((pure (! aligned)) <&&> (do
       (AlignmentEnforced ())))) : Bool)
  then (AArch64_Abort (BitVec.addInt base moffs) (← (AlignmentFault accdesc)))
  else (pure ())
  let (moffs, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (moffs, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (moffs, result) := loop_vars
      loop_vars ← do
        let result ← (( do
          let moffs := moffs
          (Elem_set result e 8 (← (AArch64_MemSingle_read (BitVec.addInt base moffs) 1 accdesc aligned))) ) : SailM (BitVec SVL) )
        let moffs : Int := (moffs +i 1)
        (pure (moffs, result))
    (pure loop_vars) ) : SailM (Int × (BitVec SVL)) )
  (ZAvector_set vec SVL result)

/-- Type quantifiers: SVL : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL SVL) -/
def execute_STR_ZA_RI__ (SVL : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckSMEAndZAEnabled ())
  let SVL := SVL
  let dim := (Int.ediv SVL 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let moffs : Int := (offset *i dim)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec := (Nat.mod ((BitVec.toNat vbase) +i offset) dim)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSME MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  if ((←((HaveTME ()) <&&> (do
       (pure ((← readReg TSTATE).depth >b 0))))) : Bool)
  then (FailTransaction TMFailure_ERR false)
  else (pure ())
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let src ← (( do (ZAvector_read vec SVL) ) : SailM (BitVec SVL) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base moffs) 16)
  if ((←((pure (! aligned)) <&&> (do
       (AlignmentEnforced ())))) : Bool)
  then (AArch64_Abort (BitVec.addInt base moffs) (← (AlignmentFault accdesc)))
  else (pure ())
  let moffs ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := moffs
    for e in [loop_e_lower:loop_e_upper:1]i do
      let moffs := loop_vars
      loop_vars ← do
        let moffs := moffs
        (AArch64_MemSingle_set (BitVec.addInt base moffs) 1 accdesc aligned (← (Elem_read src e 8)))
        (pure (moffs +i 1))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, offset : Nat, s : Nat, t : Nat, k_vertical : Bool, t = 0 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_ZA_P_RRR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (offset : Nat) (s : Nat) (t : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let addr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let moffs ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSME MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((←((AnyActiveElement mask esize) <||> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let (addr, moffs, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (addr, moffs, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (addr, moffs, result) := loop_vars
      loop_vars ← do
        let addr : (BitVec 64) := (BitVec.addInt base ((BitVec.toNat moffs) *i mbytes))
        let result ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then (do (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
          else (do (Elem_set result e esize (Zeros (n := esize)))) ) : SailM (BitVec VL) )
        let moffs : (BitVec 64) := (BitVec.addInt moffs 1)
        (pure (addr, moffs, result))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  (ZAslice_set t esize vertical slice_name VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, offset : Nat, s : Nat, t : Nat, k_vertical : Bool, List.elem t [0, 1] ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_ZA_P_RRR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (offset : Nat) (s : Nat) (t : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let addr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let moffs ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSME MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((←((AnyActiveElement mask esize) <||> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let (addr, moffs, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (addr, moffs, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (addr, moffs, result) := loop_vars
      loop_vars ← do
        let addr : (BitVec 64) := (BitVec.addInt base ((BitVec.toNat moffs) *i mbytes))
        let result ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then (do (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
          else (do (Elem_set result e esize (Zeros (n := esize)))) ) : SailM (BitVec VL) )
        let moffs : (BitVec 64) := (BitVec.addInt moffs 1)
        (pure (addr, moffs, result))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  (ZAslice_set t esize vertical slice_name VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, offset : Nat, s : Nat, t : Nat, k_vertical : Bool, List.elem t [0, 1, 2, 3] ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_ZA_P_RRR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (offset : Nat) (s : Nat) (t : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let addr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let moffs ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSME MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((←((AnyActiveElement mask esize) <||> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let (addr, moffs, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (addr, moffs, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (addr, moffs, result) := loop_vars
      loop_vars ← do
        let addr : (BitVec 64) := (BitVec.addInt base ((BitVec.toNat moffs) *i mbytes))
        let result ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then (do (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
          else (do (Elem_set result e esize (Zeros (n := esize)))) ) : SailM (BitVec VL) )
        let moffs : (BitVec 64) := (BitVec.addInt moffs 1)
        (pure (addr, moffs, result))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  (ZAslice_set t esize vertical slice_name VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, offset : Nat, s : Nat, t : Nat, k_vertical : Bool, List.elem t [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_ZA_P_RRR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (offset : Nat) (s : Nat) (t : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let addr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let moffs ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSME MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((←((AnyActiveElement mask esize) <||> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let (addr, moffs, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (addr, moffs, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (addr, moffs, result) := loop_vars
      loop_vars ← do
        let addr : (BitVec 64) := (BitVec.addInt base ((BitVec.toNat moffs) *i mbytes))
        let result ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then (do (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
          else (do (Elem_set result e esize (Zeros (n := esize)))) ) : SailM (BitVec VL) )
        let moffs : (BitVec 64) := (BitVec.addInt moffs 1)
        (pure (addr, moffs, result))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  (ZAslice_set t esize vertical slice_name VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, offset : Nat, s : Nat, t : Nat, k_vertical : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD1Q_ZA_P_RRR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (offset : Nat) (s : Nat) (t : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let addr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let moffs ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSME MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((←((AnyActiveElement mask esize) <||> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let (addr, moffs, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (addr, moffs, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (addr, moffs, result) := loop_vars
      loop_vars ← do
        let addr : (BitVec 64) := (BitVec.addInt base ((BitVec.toNat moffs) *i mbytes))
        let result ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then (do (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
          else (do (Elem_set result e esize (Zeros (n := esize)))) ) : SailM (BitVec VL) )
        let moffs : (BitVec 64) := (BitVec.addInt moffs 1)
        (pure (addr, moffs, result))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  (ZAslice_set t esize vertical slice_name VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, offset : Nat, s : Nat, t : Nat, k_vertical : Bool, t = 0 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST1B_ZA_P_RRR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (offset : Nat) (s : Nat) (t : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let addr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let moffs ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSME MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((←((AnyActiveElement mask esize) <||> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let src ← (( do (ZAslice_read t esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let (addr, moffs) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (addr, moffs)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (addr, moffs) := loop_vars
      loop_vars ← do
        let addr : (BitVec 64) := (BitVec.addInt base ((BitVec.toNat moffs) *i mbytes))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (Mem_set addr mbytes accdesc (← (Elem_read src e esize)))
        else (pure ())
        let moffs : (BitVec 64) := (BitVec.addInt moffs 1)
        (pure (addr, moffs))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, offset : Nat, s : Nat, t : Nat, k_vertical : Bool, List.elem t [0, 1] ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST1H_ZA_P_RRR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (offset : Nat) (s : Nat) (t : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let addr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let moffs ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSME MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((←((AnyActiveElement mask esize) <||> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let src ← (( do (ZAslice_read t esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let (addr, moffs) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (addr, moffs)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (addr, moffs) := loop_vars
      loop_vars ← do
        let addr : (BitVec 64) := (BitVec.addInt base ((BitVec.toNat moffs) *i mbytes))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (Mem_set addr mbytes accdesc (← (Elem_read src e esize)))
        else (pure ())
        let moffs : (BitVec 64) := (BitVec.addInt moffs 1)
        (pure (addr, moffs))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, offset : Nat, s : Nat, t : Nat, k_vertical : Bool, List.elem t [0, 1, 2, 3] ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_ZA_P_RRR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (offset : Nat) (s : Nat) (t : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let addr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let moffs ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSME MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((←((AnyActiveElement mask esize) <||> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let src ← (( do (ZAslice_read t esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let (addr, moffs) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (addr, moffs)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (addr, moffs) := loop_vars
      loop_vars ← do
        let addr : (BitVec 64) := (BitVec.addInt base ((BitVec.toNat moffs) *i mbytes))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (Mem_set addr mbytes accdesc (← (Elem_read src e esize)))
        else (pure ())
        let moffs : (BitVec 64) := (BitVec.addInt moffs 1)
        (pure (addr, moffs))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, offset : Nat, s : Nat, t : Nat, k_vertical : Bool, List.elem t [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_ZA_P_RRR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (offset : Nat) (s : Nat) (t : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let addr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let moffs ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSME MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((←((AnyActiveElement mask esize) <||> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let src ← (( do (ZAslice_read t esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let (addr, moffs) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (addr, moffs)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (addr, moffs) := loop_vars
      loop_vars ← do
        let addr : (BitVec 64) := (BitVec.addInt base ((BitVec.toNat moffs) *i mbytes))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (Mem_set addr mbytes accdesc (← (Elem_read src e esize)))
        else (pure ())
        let moffs : (BitVec 64) := (BitVec.addInt moffs 1)
        (pure (addr, moffs))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, offset : Nat, s : Nat, t : Nat, k_vertical : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST1Q_ZA_P_RRR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (offset : Nat) (s : Nat) (t : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let addr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let moffs ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSME MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((←((AnyActiveElement mask esize) <||> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let src ← (( do (ZAslice_read t esize vertical slice_name VL) ) : SailM (BitVec VL) )
  let (addr, moffs) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (dim -i 1)
    let mut loop_vars := (addr, moffs)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (addr, moffs) := loop_vars
      loop_vars ← do
        let addr : (BitVec 64) := (BitVec.addInt base ((BitVec.toNat moffs) *i mbytes))
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (Mem_set addr mbytes accdesc (← (Elem_read src e esize)))
        else (pure ())
        let moffs : (BitVec 64) := (BitVec.addInt moffs 1)
        (pure (addr, moffs))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64)) )
  (pure ())

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_ADDHA_ZA_PP_Z_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand_src ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand_acc ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_col_lower := 0
    let loop_col_upper := (dim -i 1)
    let mut loop_vars := result
    for col in [loop_col_lower:loop_col_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand_src col esize) ) : SailM (BitVec esize) )
        let loop_row_lower := 0
        let loop_row_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for row in [loop_row_lower:loop_row_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let res ← (( do (Elem_read operand_acc ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
            let res ← (( do
              if ((←((ActivePredicateElement mask1 row esize) <&&> (do
                   (ActivePredicateElement mask2 col esize)))) : Bool)
              then (pure (res + element))
              else (pure res) ) : SailM (BitVec esize) )
            (Elem_set result ((row *i dim) +i col) esize res)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_ADDHA_ZA_PP_Z_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand_src ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand_acc ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_col_lower := 0
    let loop_col_upper := (dim -i 1)
    let mut loop_vars := result
    for col in [loop_col_lower:loop_col_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand_src col esize) ) : SailM (BitVec esize) )
        let loop_row_lower := 0
        let loop_row_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for row in [loop_row_lower:loop_row_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let res ← (( do (Elem_read operand_acc ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
            let res ← (( do
              if ((←((ActivePredicateElement mask1 row esize) <&&> (do
                   (ActivePredicateElement mask2 col esize)))) : Bool)
              then (pure (res + element))
              else (pure res) ) : SailM (BitVec esize) )
            (Elem_set result ((row *i dim) +i col) esize res)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_ADDVA_ZA_PP_Z_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand_src ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand_acc ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := result
    for row in [loop_row_lower:loop_row_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand_src row esize) ) : SailM (BitVec esize) )
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let res ← (( do (Elem_read operand_acc ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
            let res ← (( do
              if ((←((ActivePredicateElement mask1 row esize) <&&> (do
                   (ActivePredicateElement mask2 col esize)))) : Bool)
              then (pure (res + element))
              else (pure res) ) : SailM (BitVec esize) )
            (Elem_set result ((row *i dim) +i col) esize res)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 64 ∧ List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_ADDVA_ZA_PP_Z_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand_src ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand_acc ← (( do (ZAtile_read VL da esize dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do (undefined_bitvector dim_dim_esize) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower := 0
    let loop_row_upper := (dim -i 1)
    let mut loop_vars := result
    for row in [loop_row_lower:loop_row_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand_src row esize) ) : SailM (BitVec esize) )
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let res ← (( do (Elem_read operand_acc ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
            let res ← (( do
              if ((←((ActivePredicateElement mask1 row esize) <&&> (do
                   (ActivePredicateElement mask2 col esize)))) : Bool)
              then (pure (res + element))
              else (pure res) ) : SailM (BitVec esize) )
            (Elem_set result ((row *i dim) +i col) esize res)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: SVL : Nat, dim_dim_esize : Nat, esize : Nat, esize = 64 ∧ (is_VL SVL) ∧ dim_dim_esize = (SVL / esize * (SVL / esize * esize)) -/
def execute_ZERO_ZA_I__ (SVL : Nat) (dim_dim_esize : Nat) (esize : Nat) (mask : (BitVec 8)) : SailM Unit := do
  (CheckSMEAndZAEnabled ())
  let SVL := SVL
  let dim := (Int.ediv SVL esize)
  let result : (BitVec dim_dim_esize) := (Zeros (n := dim_dim_esize))
  if ((←((HaveTME ()) <&&> (do
       (pure ((← readReg TSTATE).depth >b 0))))) : Bool)
  then (FailTransaction TMFailure_ERR false)
  else (pure ())
  let loop_i_lower := 0
  let loop_i_upper := 7
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if (((BitVec.join1 [(BitVec.access mask i)]) == 1#1) : Bool)
      then (ZAtile_set SVL i esize dim_dim_esize result)
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 8 ∧ d = 0 ∧ (is_VL VL) -/
def execute_MOVA_ZA2_Z_B1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
      (ZAslice_set d esize vertical (slice_name +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ List.elem d [0, 1] ∧ (is_VL VL) -/
def execute_MOVA_ZA2_Z_H1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
      (ZAslice_set d esize vertical (slice_name +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 32 ∧ List.elem d [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_MOVA_ZA2_Z_W1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
      (ZAslice_set d esize vertical (slice_name +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 64 ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_MOVA_ZA2_Z_D1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
      (ZAslice_set d esize vertical (slice_name +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 8 ∧ d = 0 ∧ (is_VL VL) -/
def execute_MOVA_ZA4_Z_B1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
      (ZAslice_set d esize vertical (slice_name +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ List.elem d [0, 1] ∧ (is_VL VL) -/
def execute_MOVA_ZA4_Z_H1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
      (ZAslice_set d esize vertical (slice_name +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 32 ∧ List.elem d [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_MOVA_ZA4_Z_W1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
      (ZAslice_set d esize vertical (slice_name +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 64 ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_MOVA_ZA4_Z_D1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  if ((((nreg == 4) && (esize == 64)) && (VL == 128)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
      (ZAslice_set d esize vertical (slice_name +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_ZA_MZ2_1 (VL : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let result ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_ZA_MZ4_1 (VL : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let result ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 2 ∧ n = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_MZ2_ZA_B1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (ZAslice_read n esize vertical (slice_name +i r) VL) ) : SailM (BitVec VL) )
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ List.elem n [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_MZ2_ZA_H1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (ZAslice_read n esize vertical (slice_name +i r) VL) ) : SailM (BitVec VL) )
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3] ∧ nreg = 2 ∧ List.elem n [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_MZ2_ZA_W1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (ZAslice_read n esize vertical (slice_name +i r) VL) ) : SailM (BitVec VL) )
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ nreg = 2 ∧ List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_MZ2_ZA_D1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (ZAslice_read n esize vertical (slice_name +i r) VL) ) : SailM (BitVec VL) )
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 4 ∧ n = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_MZ4_ZA_B1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (ZAslice_read n esize vertical (slice_name +i r) VL) ) : SailM (BitVec VL) )
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ List.elem n [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_MZ4_ZA_H1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (ZAslice_read n esize vertical (slice_name +i r) VL) ) : SailM (BitVec VL) )
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ nreg = 4 ∧ List.elem n [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_MZ4_ZA_W1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (ZAslice_read n esize vertical (slice_name +i r) VL) ) : SailM (BitVec VL) )
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ nreg = 4 ∧ List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_MZ4_ZA_D1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  if ((((nreg == 4) && (esize == 64)) && (VL == 128)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let slices := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let result ← (( do (ZAslice_read n esize vertical (slice_name +i r) VL) ) : SailM (BitVec VL) )
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_MZ_ZA2_1 (VL : Nat) (d : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let result ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        (Z_set (d +i r) VL result)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_MZ_ZA4_1 (VL : Nat) (d : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let result ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        (Z_set (d +i r) VL result)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNT1B_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNT1B_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST1B_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST1H_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST1B_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST1H_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_MZx_P_BR_2x8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_MZx_P_BR_4x4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base ((((BitVec.toNat offset) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNT1B_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNT1B_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let values_name ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := values_name
        for e in [loop_e_lower:loop_e_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let t ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars_2 := t
    for r in [loop_r_lower:loop_r_upper:1]i do
      let t := loop_vars_2
      loop_vars_2 ← do
        (Z_set t VL (GetElem?.getElem! values_name r))
        (pure (t +i tstride))
    (pure loop_vars_2) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST1B_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST1H_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST1B_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST1H_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 8 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg : Nat, tstride : Nat, tstride = 4 ∧ 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mbytes := (Int.ediv esize 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure base))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64)) ) : SailM (BitVec 64) )
  let (src, t) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (src, t)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (src, t) := loop_vars
      loop_vars ← do
        let src ← (Z_read t VL)
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := ()
        for e in [loop_e_lower:loop_e_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then
              (do
                let addr : (BitVec 64) := (BitVec.addInt base (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
            else (pure ())
        (pure loop_vars_1)
        let t : Int := (t +i tstride)
        (pure (src, t))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FADD_ZA_ZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPAdd_ZA element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FSUB_ZA_ZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPSub_ZA element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FADD_ZA_ZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPAdd_ZA element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FSUB_ZA_ZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPSub_ZA element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZi_D2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZi_D2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s esize) ) : SailM (BitVec esize) )
              let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (FPNeg element1))
                else (pure element1) ) : SailM (BitVec esize) )
              (Elem_set result e esize (← (FPMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZV_2x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (FPDotAdd_ZA sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZV_2x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (FPDotAdd_ZA sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZW_4x4 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZV_4x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZW_4x4 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (FPDotAdd_ZA sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZV_4x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (FPDotAdd_ZA sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZi_4xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (FPDotAdd_ZA sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZi_4xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (FPDotAdd_ZA sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_BFVDOT_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name 2)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1a ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
        let operand1b ← (( do (Z_read (n +i 1) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let elt1_a ← (( do (Elem_read operand1a ((2 *i e) +i r) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1b ((2 *i e) +i r) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_FVDOT_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name 2)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1a ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
        let operand1b ← (( do (Z_read (n +i 1) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let elt1_a ← (( do (Elem_read operand1a ((2 *i e) +i r) 16) ) : SailM (BitVec 16) )
              let elt1_b ← (( do (Elem_read operand1b ((2 *i e) +i r) 16) ) : SailM (BitVec 16) )
              let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16) )
              let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16) )
              let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
              let sum ← (( do (FPDotAdd_ZA sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
              (Elem_set result e 32 sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZV_1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZV_2x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZW_4x4 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZV_4x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSL_ZA_ZZV_1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSL_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSL_ZA_ZZV_2x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSL_ZA_ZZW_4x4 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSL_ZA_ZZV_4x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZi_1 (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZi_4xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_BFMLSL_ZA_ZZi_1 (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_BFMLSL_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_BFMLSL_ZA_ZZi_4xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (BFNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (BFMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLAL_ZA_ZZV_1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLAL_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLAL_ZA_ZZV_2x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLAL_ZA_ZZW_4x4 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLAL_ZA_ZZV_4x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_FMLAL_ZA_ZZi_1 (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_FMLAL_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_FMLAL_ZA_ZZi_4xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSL_ZA_ZZV_1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSL_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSL_ZA_ZZV_2x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSL_ZA_ZZW_4x4 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSL_ZA_ZZV_4x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_FMLSL_ZA_ZZi_1 (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_FMLSL_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_FMLSL_ZA_ZZi_4xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 32)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let vec := vec
          let loop_i_lower := 0
          let loop_i_upper := 1
          let mut loop_vars_1 := result
          for i in [loop_i_lower:loop_i_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let operand3 ← (( do (ZAvector_read (vec +i i) VL) ) : SailM (BitVec VL) )
              let result ← (( do
                let loop_e_lower := 0
                let loop_e_upper := (elements -i 1)
                let mut loop_vars_2 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_2
                  loop_vars_2 ← do
                    let segmentbase := (e -i (Nat.mod e eltspersegment))
                    let s := ((2 *i segmentbase) +i index)
                    let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM (BitVec 16) )
                    let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
                    let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then (do (FPNeg element1))
                      else (pure element1) ) : SailM (BitVec 16) )
                    (Elem_set result e 32 (← (FPMulAddH_ZA element3 element1 element2 (← (FPCR_read ())))))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAX_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:16715.53-16715.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMax element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAX_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:16778.53-16778.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMax element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMIN_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:16841.53-16841.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMin element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMIN_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:16904.53-16904.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMin element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAX_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:16967.53-16967.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMax element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAX_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17030.53-17030.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMax element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMIN_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17093.53-17093.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMin element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMIN_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17156.53-17156.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMin element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNM_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17219.53-17219.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMaxNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNM_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17282.53-17282.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMaxNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNM_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17345.53-17345.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMinNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNM_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17408.53-17408.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMinNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNM_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17471.53-17471.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMaxNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNM_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17534.53-17534.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMaxNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNM_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17597.53-17597.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMinNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNM_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (dn +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17660.53-17660.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMinNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCLAMP_MZ_ZZ_2 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do (Z_read (d +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17725.53-17725.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMinNum (← (FPMaxNum element1 element3 (← (FPCR_read ())))) element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCLAMP_MZ_ZZ_4 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do (Z_read (d +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
            let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
            sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sme.sail:17792.53-17792.54"
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (FPMinNum (← (FPMaxNum element1 element3 (← (FPCR_read ())))) element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCVT_Z_MZ2__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let operand1 ← (( do (Z_read (n +i 0) VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read (n +i 1) VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
        let element2 ← (( do (Elem_read operand2 e 32) ) : SailM (BitVec 32) )
        let res1 ← (( do (FPConvertBF__1 element1 (← (FPCR_read ()))) ) : SailM (BitVec 16) )
        let res2 ← (( do (FPConvertBF__1 element2 (← (FPCR_read ()))) ) : SailM (BitVec 16) )
        let result ← (Elem_set result e 16 res1)
        (Elem_set result (elements +i e) 16 res2)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_MZ2__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let operand1 ← (( do (Z_read (n +i 0) VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read (n +i 1) VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
        let element2 ← (( do (Elem_read operand2 e 32) ) : SailM (BitVec 32) )
        let res1 ← (( do (FPConvertSVE__1 element1 (← (FPCR_read ())) 16) ) : SailM (BitVec 16) )
        let res2 ← (( do (FPConvertSVE__1 element2 (← (FPCR_read ())) 16) ) : SailM (BitVec 16) )
        let result ← (Elem_set result e 16 res1)
        (Elem_set result (elements +i e) 16 res2)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCVTN_Z_MZ2__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let operand1 ← (( do (Z_read (n +i 0) VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read (n +i 1) VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
        let element2 ← (( do (Elem_read operand2 e 32) ) : SailM (BitVec 32) )
        let res1 ← (( do (FPConvertBF__1 element1 (← (FPCR_read ()))) ) : SailM (BitVec 16) )
        let res2 ← (( do (FPConvertBF__1 element2 (← (FPCR_read ()))) ) : SailM (BitVec 16) )
        let result ← (Elem_set result ((2 *i e) +i 0) 16 res1)
        (Elem_set result ((2 *i e) +i 1) 16 res2)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTN_Z_MZ2__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let operand1 ← (( do (Z_read (n +i 0) VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read (n +i 1) VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
        let element2 ← (( do (Elem_read operand2 e 32) ) : SailM (BitVec 32) )
        let res1 ← (( do (FPConvertSVE__1 element1 (← (FPCR_read ())) 16) ) : SailM (BitVec 16) )
        let res2 ← (( do (FPConvertSVE__1 element2 (← (FPCR_read ())) 16) ) : SailM (BitVec 16) )
        let result ← (Elem_set result ((2 *i e) +i 0) 16 res1)
        (Elem_set result ((2 *i e) +i 1) 16 res2)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_MZ_Z_2 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPToFixed element 0 is_unsigned (← (FPCR_read ())) rounding 32))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_MZ_Z_4 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPToFixed element 0 is_unsigned (← (FPCR_read ())) rounding 32))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_MZ_Z_2 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPToFixed element 0 is_unsigned (← (FPCR_read ())) rounding 32))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZS_MZ_Z_4 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPToFixed element 0 is_unsigned (← (FPCR_read ())) rounding 32))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_MZ_Z_2 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FixedToFP element 0 is_unsigned (← (FPCR_read ())) rounding 32))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_MZ_Z_4 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FixedToFP element 0 is_unsigned (← (FPCR_read ())) rounding 32))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_MZ_Z_2 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FixedToFP element 0 is_unsigned (← (FPCR_read ())) rounding 32))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_MZ_Z_4 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FixedToFP element 0 is_unsigned (← (FPCR_read ())) rounding 32))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTA_MZ_Z_2 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTM_MZ_Z_2 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTN_MZ_Z_2 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTP_MZ_Z_2 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTA_MZ_Z_4 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTM_MZ_Z_4 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTN_MZ_Z_4 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTP_MZ_Z_4 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 32)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 32 (← (FPRoundInt element (← (FPCR_read ())) rounding exact))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_ADD_ZA_ZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 + element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SUB_ZA_ZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 - element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_ADD_ZA_ZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 + element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SUB_ZA_ZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 - element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_ADD_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 + element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SUB_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 - element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_ADD_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 + element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SUB_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 - element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_ADD_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 + element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SUB_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 - element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_ADD_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 + element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SUB_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let element1 ← (( do (Elem_read operand1 e esize) ) : SailM (BitVec esize) )
              let element2 ← (( do (Elem_read operand2 e esize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (element1 - element2))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UDOT_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    (pure (BitVec.addInt sum (element1 *i element2)))
                (pure loop_vars_2) ) : SailM (BitVec esize) )
              (Elem_set result e esize sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SDOT_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    (pure (BitVec.addInt sum (element1 *i element2)))
                (pure loop_vars_2) ) : SailM (BitVec esize) )
              (Elem_set result e esize sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USDOT_ZA_ZZW_S2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    (pure (BitVec.addInt sum (element1 *i element2)))
                (pure loop_vars_2) ) : SailM (BitVec esize) )
              (Elem_set result e esize sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UDOT_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (Nat.mod (n +i r) 32) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
        let operand3 ← (( do
          let vec := vec
          (ZAvector_read vec VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    (pure (BitVec.addInt sum (element1 *i element2)))
                (pure loop_vars_2) ) : SailM (BitVec esize) )
              (Elem_set result e esize sum)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())


