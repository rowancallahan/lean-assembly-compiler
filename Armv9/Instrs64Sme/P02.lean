import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.Prelude
import Armv9.Builtins
import Armv9.V8Base
import Armv9.Instrs64Sme.P00
import Armv9.Instrs64Sme.P01

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

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMIN_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMin element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMIN_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMin element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMAXNM_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMaxNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMAXNM_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMaxNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMINNM_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMinNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMINNM_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMinNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMAXNM_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMaxNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMAXNM_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMaxNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMINNM_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMinNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMINNM_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMinNum element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_MZ2_Z__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector (2 *i VL)) ) : SailM (BitVec (2 * VL)) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element ← (( do (Elem_read operand e 16) ) : SailM (BitVec 16) )
        let res ← (( do (FPConvertSVE__1 element (← (FPCR_read ())) 32) ) : SailM (BitVec 32) )
        (Elem_set result e 32 res)
    (pure loop_vars) ) : SailM (BitVec (2 * VL)) )
  (Z_set (d +i 0) VL (Sail.BitVec.extractLsb result (VL -i 1) 0))
  (Z_set (d +i 1) VL (Sail.BitVec.extractLsb result ((2 *i VL) -i 1) VL))

/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTL_MZ2_Z__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL 32)
  let operand ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let result0 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result1 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result0, result1) ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := (result0, result1)
    for p in [loop_p_lower:loop_p_upper:1]i do
      let (result0, result1) := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand ((2 *i p) +i 0) 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand ((2 *i p) +i 1) 16) ) : SailM (BitVec 16) )
        let res1 ← (( do (FPConvertSVE__1 element1 (← (FPCR_read ())) 32) ) : SailM (BitVec 32) )
        let res2 ← (( do (FPConvertSVE__1 element2 (← (FPCR_read ())) 32) ) : SailM (BitVec 32) )
        let result0 ← (Elem_set result0 p 32 res1)
        let result1 ← (Elem_set result1 p 32 res2)
        (pure (result0, result1))
    (pure loop_vars) ) : SailM ((BitVec VL) × (BitVec VL)) )
  (Z_set (d +i 0) VL result0)
  (Z_set (d +i 1) VL result1)

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCLAMP_MZ_ZZ_2 (VL : Nat) (d : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMinNum (← (BFMaxNum element1 element3 (← (FPCR_read ())))) element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCLAMP_MZ_ZZ_4 (VL : Nat) (d : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
            let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
            let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMinNum (← (BFMaxNum element1 element3 (← (FPCR_read ())))) element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

def decode_FMOPA_ZA_PP_ZZ_32 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 => (execute_FMOPA_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op)
  | 256 => (execute_FMOPA_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op)
  | 512 => (execute_FMOPA_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op)
  | 1024 => (execute_FMOPA_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op)
  | 2048 => (execute_FMOPA_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op)
  | _ => (pure ())

def decode_FMOPS_ZA_PP_ZZ_32 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 => (execute_FMOPS_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op)
  | 256 => (execute_FMOPS_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op)
  | 512 => (execute_FMOPS_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op)
  | 1024 => (execute_FMOPS_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op)
  | 2048 => (execute_FMOPS_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op)
  | _ => (pure ())

def decode_FMOPA_ZA_PP_ZZ_64 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF64F64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 => (execute_FMOPA_ZA_PP_ZZ_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op)
  | 256 => (execute_FMOPA_ZA_PP_ZZ_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op)
  | 512 => (execute_FMOPA_ZA_PP_ZZ_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op)
  | 1024 => (execute_FMOPA_ZA_PP_ZZ_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op)
  | 2048 => (execute_FMOPA_ZA_PP_ZZ_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op)
  | _ => (pure ())

def decode_FMOPS_ZA_PP_ZZ_64 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF64F64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 => (execute_FMOPS_ZA_PP_ZZ_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op)
  | 256 => (execute_FMOPS_ZA_PP_ZZ_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op)
  | 512 => (execute_FMOPS_ZA_PP_ZZ_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op)
  | 1024 => (execute_FMOPS_ZA_PP_ZZ_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op)
  | 2048 => (execute_FMOPS_ZA_PP_ZZ_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op)
  | _ => (pure ())

def decode_BFMOPA_ZA32_PP_ZZ__ (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 => (execute_BFMOPA_ZA32_PP_ZZ__ 128 (((Int.ediv 128 32) *i (Int.ediv 128 32)) *i 32) a b da m n sub_op)
  | 256 => (execute_BFMOPA_ZA32_PP_ZZ__ 256 (((Int.ediv 256 32) *i (Int.ediv 256 32)) *i 32) a b da m n sub_op)
  | 512 => (execute_BFMOPA_ZA32_PP_ZZ__ 512 (((Int.ediv 512 32) *i (Int.ediv 512 32)) *i 32) a b da m n sub_op)
  | 1024 => (execute_BFMOPA_ZA32_PP_ZZ__ 1024 (((Int.ediv 1024 32) *i (Int.ediv 1024 32)) *i 32) a b da m n sub_op)
  | 2048 => (execute_BFMOPA_ZA32_PP_ZZ__ 2048 (((Int.ediv 2048 32) *i (Int.ediv 2048 32)) *i 32) a b da m n sub_op)
  | _ => (pure ())

def decode_BFMOPS_ZA32_PP_ZZ__ (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 => (execute_BFMOPS_ZA32_PP_ZZ__ 128 (((Int.ediv 128 32) *i (Int.ediv 128 32)) *i 32) a b da m n sub_op)
  | 256 => (execute_BFMOPS_ZA32_PP_ZZ__ 256 (((Int.ediv 256 32) *i (Int.ediv 256 32)) *i 32) a b da m n sub_op)
  | 512 => (execute_BFMOPS_ZA32_PP_ZZ__ 512 (((Int.ediv 512 32) *i (Int.ediv 512 32)) *i 32) a b da m n sub_op)
  | 1024 => (execute_BFMOPS_ZA32_PP_ZZ__ 1024 (((Int.ediv 1024 32) *i (Int.ediv 1024 32)) *i 32) a b da m n sub_op)
  | 2048 => (execute_BFMOPS_ZA32_PP_ZZ__ 2048 (((Int.ediv 2048 32) *i (Int.ediv 2048 32)) *i 32) a b da m n sub_op)
  | _ => (pure ())

def decode_FMOPA_ZA32_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 => (execute_FMOPA_ZA32_PP_ZZ_16 128 (((Int.ediv 128 32) *i (Int.ediv 128 32)) *i 32) a b da m n sub_op)
  | 256 => (execute_FMOPA_ZA32_PP_ZZ_16 256 (((Int.ediv 256 32) *i (Int.ediv 256 32)) *i 32) a b da m n sub_op)
  | 512 => (execute_FMOPA_ZA32_PP_ZZ_16 512 (((Int.ediv 512 32) *i (Int.ediv 512 32)) *i 32) a b da m n sub_op)
  | 1024 => (execute_FMOPA_ZA32_PP_ZZ_16 1024 (((Int.ediv 1024 32) *i (Int.ediv 1024 32)) *i 32) a b da m n sub_op)
  | 2048 => (execute_FMOPA_ZA32_PP_ZZ_16 2048 (((Int.ediv 2048 32) *i (Int.ediv 2048 32)) *i 32) a b da m n sub_op)
  | _ => (pure ())

def decode_FMOPS_ZA32_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 => (execute_FMOPS_ZA32_PP_ZZ_16 128 (((Int.ediv 128 32) *i (Int.ediv 128 32)) *i 32) a b da m n sub_op)
  | 256 => (execute_FMOPS_ZA32_PP_ZZ_16 256 (((Int.ediv 256 32) *i (Int.ediv 256 32)) *i 32) a b da m n sub_op)
  | 512 => (execute_FMOPS_ZA32_PP_ZZ_16 512 (((Int.ediv 512 32) *i (Int.ediv 512 32)) *i 32) a b da m n sub_op)
  | 1024 => (execute_FMOPS_ZA32_PP_ZZ_16 1024 (((Int.ediv 1024 32) *i (Int.ediv 1024 32)) *i 32) a b da m n sub_op)
  | 2048 => (execute_FMOPS_ZA32_PP_ZZ_16 2048 (((Int.ediv 2048 32) *i (Int.ediv 2048 32)) *i 32) a b da m n sub_op)
  | _ => (pure ())

def decode_SMOPA_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMOPA_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_SMOPA_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_SMOPA_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_SMOPA_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_SMOPA_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_SUMOPA_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := true
  match VL with
  | 128 => (execute_SUMOPA_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_SUMOPA_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_SUMOPA_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_SUMOPA_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_SUMOPA_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_USMOPA_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := false
  match VL with
  | 128 => (execute_USMOPA_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_USMOPA_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_USMOPA_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_USMOPA_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_USMOPA_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_UMOPA_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMOPA_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_UMOPA_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_UMOPA_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_UMOPA_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_UMOPA_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_SMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMOPS_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_SMOPS_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_SMOPS_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_SMOPS_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_SMOPS_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_SUMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := true
  match VL with
  | 128 => (execute_SUMOPS_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_SUMOPS_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_SUMOPS_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_SUMOPS_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_SUMOPS_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_USMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := false
  match VL with
  | 128 => (execute_USMOPS_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_USMOPS_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_USMOPS_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_USMOPS_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_USMOPS_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_UMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMOPS_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_UMOPS_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_UMOPS_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_UMOPS_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_UMOPS_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_SMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEI16I64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMOPA_ZA_PP_ZZ_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_SMOPA_ZA_PP_ZZ_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_SMOPA_ZA_PP_ZZ_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_SMOPA_ZA_PP_ZZ_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_SMOPA_ZA_PP_ZZ_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_SUMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEI16I64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := true
  match VL with
  | 128 => (execute_SUMOPA_ZA_PP_ZZ_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_SUMOPA_ZA_PP_ZZ_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_SUMOPA_ZA_PP_ZZ_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_SUMOPA_ZA_PP_ZZ_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_SUMOPA_ZA_PP_ZZ_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_USMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEI16I64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := false
  match VL with
  | 128 => (execute_USMOPA_ZA_PP_ZZ_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_USMOPA_ZA_PP_ZZ_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_USMOPA_ZA_PP_ZZ_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_USMOPA_ZA_PP_ZZ_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_USMOPA_ZA_PP_ZZ_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_UMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEI16I64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMOPA_ZA_PP_ZZ_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_UMOPA_ZA_PP_ZZ_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_UMOPA_ZA_PP_ZZ_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_UMOPA_ZA_PP_ZZ_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_UMOPA_ZA_PP_ZZ_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_SMOPS_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEI16I64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMOPS_ZA_PP_ZZ_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_SMOPS_ZA_PP_ZZ_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_SMOPS_ZA_PP_ZZ_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_SMOPS_ZA_PP_ZZ_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_SMOPS_ZA_PP_ZZ_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_SUMOPS_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEI16I64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := true
  match VL with
  | 128 => (execute_SUMOPS_ZA_PP_ZZ_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_SUMOPS_ZA_PP_ZZ_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_SUMOPS_ZA_PP_ZZ_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_SUMOPS_ZA_PP_ZZ_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_SUMOPS_ZA_PP_ZZ_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_USMOPS_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEI16I64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := false
  match VL with
  | 128 => (execute_USMOPS_ZA_PP_ZZ_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_USMOPS_ZA_PP_ZZ_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_USMOPS_ZA_PP_ZZ_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_USMOPS_ZA_PP_ZZ_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_USMOPS_ZA_PP_ZZ_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_UMOPS_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEI16I64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMOPS_ZA_PP_ZZ_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 256 => (execute_UMOPS_ZA_PP_ZZ_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 512 => (execute_UMOPS_ZA_PP_ZZ_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 1024 => (execute_UMOPS_ZA_PP_ZZ_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | 2048 => (execute_UMOPS_ZA_PP_ZZ_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n op1_unsigned op2_unsigned sub_op)
  | _ => (pure ())

def decode_MOVA_ZA_P_RZ_B (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (off4 : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat Zn)
  let d := 0
  let offset := (BitVec.toNat off4)
  let esize := 8
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA_P_RZ_B 128 d esize g n offset s vertical)
  | 256 => (execute_MOVA_ZA_P_RZ_B 256 d esize g n offset s vertical)
  | 512 => (execute_MOVA_ZA_P_RZ_B 512 d esize g n offset s vertical)
  | 1024 => (execute_MOVA_ZA_P_RZ_B 1024 d esize g n offset s vertical)
  | 2048 => (execute_MOVA_ZA_P_RZ_B 2048 d esize g n offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA_P_RZ_H (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ZAd : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat ZAd)
  let offset := (BitVec.toNat off3)
  let esize := 16
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA_P_RZ_H 128 d esize g n offset s vertical)
  | 256 => (execute_MOVA_ZA_P_RZ_H 256 d esize g n offset s vertical)
  | 512 => (execute_MOVA_ZA_P_RZ_H 512 d esize g n offset s vertical)
  | 1024 => (execute_MOVA_ZA_P_RZ_H 1024 d esize g n offset s vertical)
  | 2048 => (execute_MOVA_ZA_P_RZ_H 2048 d esize g n offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA_P_RZ_W (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ZAd : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat ZAd)
  let offset := (BitVec.toNat off2)
  let esize := 32
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA_P_RZ_W 128 d esize g n offset s vertical)
  | 256 => (execute_MOVA_ZA_P_RZ_W 256 d esize g n offset s vertical)
  | 512 => (execute_MOVA_ZA_P_RZ_W 512 d esize g n offset s vertical)
  | 1024 => (execute_MOVA_ZA_P_RZ_W 1024 d esize g n offset s vertical)
  | 2048 => (execute_MOVA_ZA_P_RZ_W 2048 d esize g n offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA_P_RZ_D (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ZAd : (BitVec 3)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat ZAd)
  let offset := (BitVec.toNat o1)
  let esize := 64
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA_P_RZ_D 128 d esize g n offset s vertical)
  | 256 => (execute_MOVA_ZA_P_RZ_D 256 d esize g n offset s vertical)
  | 512 => (execute_MOVA_ZA_P_RZ_D 512 d esize g n offset s vertical)
  | 1024 => (execute_MOVA_ZA_P_RZ_D 1024 d esize g n offset s vertical)
  | 2048 => (execute_MOVA_ZA_P_RZ_D 2048 d esize g n offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA_P_RZ_Q (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ZAd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat ZAd)
  let offset := 0
  let esize := 128
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA_P_RZ_Q 128 d esize g n offset s vertical)
  | 256 => (execute_MOVA_ZA_P_RZ_Q 256 d esize g n offset s vertical)
  | 512 => (execute_MOVA_ZA_P_RZ_Q 512 d esize g n offset s vertical)
  | 1024 => (execute_MOVA_ZA_P_RZ_Q 1024 d esize g n offset s vertical)
  | 2048 => (execute_MOVA_ZA_P_RZ_Q 2048 d esize g n offset s vertical)
  | _ => (pure ())

def decode_MOVA_Z_P_RZA_B (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (off4 : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := 0
  let offset := (BitVec.toNat off4)
  let esize := 8
  let d := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_Z_P_RZA_B 128 d esize g n offset s vertical)
  | 256 => (execute_MOVA_Z_P_RZA_B 256 d esize g n offset s vertical)
  | 512 => (execute_MOVA_Z_P_RZA_B 512 d esize g n offset s vertical)
  | 1024 => (execute_MOVA_Z_P_RZA_B 1024 d esize g n offset s vertical)
  | 2048 => (execute_MOVA_Z_P_RZA_B 2048 d esize g n offset s vertical)
  | _ => (pure ())

def decode_MOVA_Z_P_RZA_H (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (ZAn : (BitVec 1)) (off3 : (BitVec 3)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat off3)
  let esize := 16
  let d := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_Z_P_RZA_H 128 d esize g n offset s vertical)
  | 256 => (execute_MOVA_Z_P_RZA_H 256 d esize g n offset s vertical)
  | 512 => (execute_MOVA_Z_P_RZA_H 512 d esize g n offset s vertical)
  | 1024 => (execute_MOVA_Z_P_RZA_H 1024 d esize g n offset s vertical)
  | 2048 => (execute_MOVA_Z_P_RZA_H 2048 d esize g n offset s vertical)
  | _ => (pure ())

def decode_MOVA_Z_P_RZA_W (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (ZAn : (BitVec 2)) (off2 : (BitVec 2)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat off2)
  let esize := 32
  let d := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_Z_P_RZA_W 128 d esize g n offset s vertical)
  | 256 => (execute_MOVA_Z_P_RZA_W 256 d esize g n offset s vertical)
  | 512 => (execute_MOVA_Z_P_RZA_W 512 d esize g n offset s vertical)
  | 1024 => (execute_MOVA_Z_P_RZA_W 1024 d esize g n offset s vertical)
  | 2048 => (execute_MOVA_Z_P_RZA_W 2048 d esize g n offset s vertical)
  | _ => (pure ())

def decode_MOVA_Z_P_RZA_D (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (ZAn : (BitVec 3)) (o1 : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat o1)
  let esize := 64
  let d := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_Z_P_RZA_D 128 d esize g n offset s vertical)
  | 256 => (execute_MOVA_Z_P_RZA_D 256 d esize g n offset s vertical)
  | 512 => (execute_MOVA_Z_P_RZA_D 512 d esize g n offset s vertical)
  | 1024 => (execute_MOVA_Z_P_RZA_D 1024 d esize g n offset s vertical)
  | 2048 => (execute_MOVA_Z_P_RZA_D 2048 d esize g n offset s vertical)
  | _ => (pure ())

def decode_MOVA_Z_P_RZA_Q (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (ZAn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat ZAn)
  let offset := 0
  let esize := 128
  let d := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_Z_P_RZA_Q 128 d esize g n offset s vertical)
  | 256 => (execute_MOVA_Z_P_RZA_Q 256 d esize g n offset s vertical)
  | 512 => (execute_MOVA_Z_P_RZA_Q 512 d esize g n offset s vertical)
  | 1024 => (execute_MOVA_Z_P_RZA_Q 1024 d esize g n offset s vertical)
  | 2048 => (execute_MOVA_Z_P_RZA_Q 2048 d esize g n offset s vertical)
  | _ => (pure ())

def decode_LDR_ZA_RI__ (Rv : (BitVec 2)) (Rn : (BitVec 5)) (off4 : (BitVec 4)) : SailM Unit := do
  let SVL ← do (CurrentSVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let v := (BitVec.toNat (0b011#3 +++ Rv))
  let offset := (BitVec.toNat off4)
  match SVL with
  | 128 => (execute_LDR_ZA_RI__ 128 n offset v)
  | 256 => (execute_LDR_ZA_RI__ 256 n offset v)
  | 512 => (execute_LDR_ZA_RI__ 512 n offset v)
  | 1024 => (execute_LDR_ZA_RI__ 1024 n offset v)
  | 2048 => (execute_LDR_ZA_RI__ 2048 n offset v)
  | _ => (pure ())

def decode_STR_ZA_RI__ (Rv : (BitVec 2)) (Rn : (BitVec 5)) (off4 : (BitVec 4)) : SailM Unit := do
  let SVL ← do (CurrentSVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let v := (BitVec.toNat (0b011#3 +++ Rv))
  let offset := (BitVec.toNat off4)
  match SVL with
  | 128 => (execute_STR_ZA_RI__ 128 n offset v)
  | 256 => (execute_STR_ZA_RI__ 256 n offset v)
  | 512 => (execute_STR_ZA_RI__ 512 n offset v)
  | 1024 => (execute_STR_ZA_RI__ 1024 n offset v)
  | 2048 => (execute_STR_ZA_RI__ 2048 n offset v)
  | _ => (pure ())

def decode_LD1B_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (off4 : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (0#1 +++ Pg))
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let t := 0
  let offset := (BitVec.toNat off4)
  let esize := 8
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_LD1B_ZA_P_RRR__ 128 esize g m n offset s t vertical)
  | 256 => (execute_LD1B_ZA_P_RRR__ 256 esize g m n offset s t vertical)
  | 512 => (execute_LD1B_ZA_P_RRR__ 512 esize g m n offset s t vertical)
  | 1024 => (execute_LD1B_ZA_P_RRR__ 1024 esize g m n offset s t vertical)
  | 2048 => (execute_LD1B_ZA_P_RRR__ 2048 esize g m n offset s t vertical)
  | _ => (pure ())

def decode_LD1H_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (0#1 +++ Pg))
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let t := (BitVec.toNat ZAt)
  let offset := (BitVec.toNat off3)
  let esize := 16
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_LD1H_ZA_P_RRR__ 128 esize g m n offset s t vertical)
  | 256 => (execute_LD1H_ZA_P_RRR__ 256 esize g m n offset s t vertical)
  | 512 => (execute_LD1H_ZA_P_RRR__ 512 esize g m n offset s t vertical)
  | 1024 => (execute_LD1H_ZA_P_RRR__ 1024 esize g m n offset s t vertical)
  | 2048 => (execute_LD1H_ZA_P_RRR__ 2048 esize g m n offset s t vertical)
  | _ => (pure ())

def decode_LD1W_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (0#1 +++ Pg))
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let t := (BitVec.toNat ZAt)
  let offset := (BitVec.toNat off2)
  let esize := 32
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_LD1W_ZA_P_RRR__ 128 esize g m n offset s t vertical)
  | 256 => (execute_LD1W_ZA_P_RRR__ 256 esize g m n offset s t vertical)
  | 512 => (execute_LD1W_ZA_P_RRR__ 512 esize g m n offset s t vertical)
  | 1024 => (execute_LD1W_ZA_P_RRR__ 1024 esize g m n offset s t vertical)
  | 2048 => (execute_LD1W_ZA_P_RRR__ 2048 esize g m n offset s t vertical)
  | _ => (pure ())

def decode_LD1D_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 3)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (0#1 +++ Pg))
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let t := (BitVec.toNat ZAt)
  let offset := (BitVec.toNat o1)
  let esize := 64
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_LD1D_ZA_P_RRR__ 128 esize g m n offset s t vertical)
  | 256 => (execute_LD1D_ZA_P_RRR__ 256 esize g m n offset s t vertical)
  | 512 => (execute_LD1D_ZA_P_RRR__ 512 esize g m n offset s t vertical)
  | 1024 => (execute_LD1D_ZA_P_RRR__ 1024 esize g m n offset s t vertical)
  | 2048 => (execute_LD1D_ZA_P_RRR__ 2048 esize g m n offset s t vertical)
  | _ => (pure ())

def decode_LD1Q_ZA_P_RRR__ (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (0#1 +++ Pg))
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let t := (BitVec.toNat ZAt)
  let offset := 0
  let esize := 128
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_LD1Q_ZA_P_RRR__ 128 esize g m n offset s t vertical)
  | 256 => (execute_LD1Q_ZA_P_RRR__ 256 esize g m n offset s t vertical)
  | 512 => (execute_LD1Q_ZA_P_RRR__ 512 esize g m n offset s t vertical)
  | 1024 => (execute_LD1Q_ZA_P_RRR__ 1024 esize g m n offset s t vertical)
  | 2048 => (execute_LD1Q_ZA_P_RRR__ 2048 esize g m n offset s t vertical)
  | _ => (pure ())

def decode_ST1B_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (off4 : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (0#1 +++ Pg))
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let t := 0
  let offset := (BitVec.toNat off4)
  let esize := 8
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_ST1B_ZA_P_RRR__ 128 esize g m n offset s t vertical)
  | 256 => (execute_ST1B_ZA_P_RRR__ 256 esize g m n offset s t vertical)
  | 512 => (execute_ST1B_ZA_P_RRR__ 512 esize g m n offset s t vertical)
  | 1024 => (execute_ST1B_ZA_P_RRR__ 1024 esize g m n offset s t vertical)
  | 2048 => (execute_ST1B_ZA_P_RRR__ 2048 esize g m n offset s t vertical)
  | _ => (pure ())

def decode_ST1H_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (0#1 +++ Pg))
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let t := (BitVec.toNat ZAt)
  let offset := (BitVec.toNat off3)
  let esize := 16
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_ST1H_ZA_P_RRR__ 128 esize g m n offset s t vertical)
  | 256 => (execute_ST1H_ZA_P_RRR__ 256 esize g m n offset s t vertical)
  | 512 => (execute_ST1H_ZA_P_RRR__ 512 esize g m n offset s t vertical)
  | 1024 => (execute_ST1H_ZA_P_RRR__ 1024 esize g m n offset s t vertical)
  | 2048 => (execute_ST1H_ZA_P_RRR__ 2048 esize g m n offset s t vertical)
  | _ => (pure ())

def decode_ST1W_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (0#1 +++ Pg))
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let t := (BitVec.toNat ZAt)
  let offset := (BitVec.toNat off2)
  let esize := 32
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_ST1W_ZA_P_RRR__ 128 esize g m n offset s t vertical)
  | 256 => (execute_ST1W_ZA_P_RRR__ 256 esize g m n offset s t vertical)
  | 512 => (execute_ST1W_ZA_P_RRR__ 512 esize g m n offset s t vertical)
  | 1024 => (execute_ST1W_ZA_P_RRR__ 1024 esize g m n offset s t vertical)
  | 2048 => (execute_ST1W_ZA_P_RRR__ 2048 esize g m n offset s t vertical)
  | _ => (pure ())

def decode_ST1D_ZA_P_RRR__ (msz : (BitVec 2)) (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 3)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (0#1 +++ Pg))
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let t := (BitVec.toNat ZAt)
  let offset := (BitVec.toNat o1)
  let esize := 64
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_ST1D_ZA_P_RRR__ 128 esize g m n offset s t vertical)
  | 256 => (execute_ST1D_ZA_P_RRR__ 256 esize g m n offset s t vertical)
  | 512 => (execute_ST1D_ZA_P_RRR__ 512 esize g m n offset s t vertical)
  | 1024 => (execute_ST1D_ZA_P_RRR__ 1024 esize g m n offset s t vertical)
  | 2048 => (execute_ST1D_ZA_P_RRR__ 2048 esize g m n offset s t vertical)
  | _ => (pure ())

def decode_ST1Q_ZA_P_RRR__ (Rm : (BitVec 5)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (ZAt : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (0#1 +++ Pg))
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let t := (BitVec.toNat ZAt)
  let offset := 0
  let esize := 128
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_ST1Q_ZA_P_RRR__ 128 esize g m n offset s t vertical)
  | 256 => (execute_ST1Q_ZA_P_RRR__ 256 esize g m n offset s t vertical)
  | 512 => (execute_ST1Q_ZA_P_RRR__ 512 esize g m n offset s t vertical)
  | 1024 => (execute_ST1Q_ZA_P_RRR__ 1024 esize g m n offset s t vertical)
  | 2048 => (execute_ST1Q_ZA_P_RRR__ 2048 esize g m n offset s t vertical)
  | _ => (pure ())

def decode_ADDHA_ZA_PP_Z_32 (V : (BitVec 1)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let da := (BitVec.toNat ZAda)
  match VL with
  | 128 => (execute_ADDHA_ZA_PP_Z_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize n)
  | 256 => (execute_ADDHA_ZA_PP_Z_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize n)
  | 512 => (execute_ADDHA_ZA_PP_Z_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize n)
  | 1024 => (execute_ADDHA_ZA_PP_Z_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize n)
  | 2048 => (execute_ADDHA_ZA_PP_Z_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize n)
  | _ => (pure ())

def decode_ADDHA_ZA_PP_Z_64 (V : (BitVec 1)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEI16I64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let da := (BitVec.toNat ZAda)
  match VL with
  | 128 => (execute_ADDHA_ZA_PP_Z_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize n)
  | 256 => (execute_ADDHA_ZA_PP_Z_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize n)
  | 512 => (execute_ADDHA_ZA_PP_Z_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize n)
  | 1024 => (execute_ADDHA_ZA_PP_Z_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize n)
  | 2048 => (execute_ADDHA_ZA_PP_Z_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize n)
  | _ => (pure ())

def decode_ADDVA_ZA_PP_Z_32 (V : (BitVec 1)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let da := (BitVec.toNat ZAda)
  match VL with
  | 128 => (execute_ADDVA_ZA_PP_Z_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize n)
  | 256 => (execute_ADDVA_ZA_PP_Z_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize n)
  | 512 => (execute_ADDVA_ZA_PP_Z_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize n)
  | 1024 => (execute_ADDVA_ZA_PP_Z_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize n)
  | 2048 => (execute_ADDVA_ZA_PP_Z_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize n)
  | _ => (pure ())

def decode_ADDVA_ZA_PP_Z_64 (V : (BitVec 1)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEI16I64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let da := (BitVec.toNat ZAda)
  match VL with
  | 128 => (execute_ADDVA_ZA_PP_Z_64 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize n)
  | 256 => (execute_ADDVA_ZA_PP_Z_64 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize n)
  | 512 => (execute_ADDVA_ZA_PP_Z_64 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize n)
  | 1024 => (execute_ADDVA_ZA_PP_Z_64 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize n)
  | 2048 => (execute_ADDVA_ZA_PP_Z_64 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize n)
  | _ => (pure ())

def decode_ZERO_ZA_I__ (imm8 : (BitVec 8)) : SailM Unit := do
  let SVL ← do (CurrentSVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let mask : (BitVec 8) := imm8
  let esize := 64
  match SVL with
  | 128 => (execute_ZERO_ZA_I__ 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) esize mask)
  | 256 => (execute_ZERO_ZA_I__ 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) esize mask)
  | 512 => (execute_ZERO_ZA_I__ 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) esize mask)
  | 1024 => (execute_ZERO_ZA_I__ 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) esize mask)
  | 2048 => (execute_ZERO_ZA_I__ 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) esize mask)
  | _ => (pure ())

def decode_MOVA_ZA2_Z_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 8
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := 0
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA2_Z_B1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_ZA2_Z_B1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_ZA2_Z_B1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_ZA2_Z_B1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_ZA2_Z_B1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA2_Z_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 4)) (ZAd : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat ZAd)
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA2_Z_H1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_ZA2_Z_H1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_ZA2_Z_H1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_ZA2_Z_H1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_ZA2_Z_H1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA2_Z_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 4)) (ZAd : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat ZAd)
  let offset := (BitVec.toNat (o1 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA2_Z_W1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_ZA2_Z_W1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_ZA2_Z_W1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_ZA2_Z_W1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_ZA2_Z_W1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA2_Z_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 4)) (ZAd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat ZAd)
  let offset := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA2_Z_D1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_ZA2_Z_D1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_ZA2_Z_D1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_ZA2_Z_D1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_ZA2_Z_D1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA4_Z_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 3)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 8
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := 0
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA4_Z_B1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_ZA4_Z_B1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_ZA4_Z_B1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_ZA4_Z_B1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_ZA4_Z_B1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA4_Z_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 3)) (ZAd : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat ZAd)
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA4_Z_H1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_ZA4_Z_H1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_ZA4_Z_H1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_ZA4_Z_H1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_ZA4_Z_H1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA4_Z_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 3)) (ZAd : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat ZAd)
  let offset := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA4_Z_W1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_ZA4_Z_W1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_ZA4_Z_W1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_ZA4_Z_W1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_ZA4_Z_W1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA4_Z_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 3)) (ZAd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat ZAd)
  let offset := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_ZA4_Z_D1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_ZA4_Z_D1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_ZA4_Z_D1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_ZA4_Z_D1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_ZA4_Z_D1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_ZA_MZ2_1 (Rv : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat off3)
  let n := (BitVec.toNat (Zn +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_MOVA_ZA_MZ2_1 128 n nreg offset v)
  | 256 => (execute_MOVA_ZA_MZ2_1 256 n nreg offset v)
  | 512 => (execute_MOVA_ZA_MZ2_1 512 n nreg offset v)
  | 1024 => (execute_MOVA_ZA_MZ2_1 1024 n nreg offset v)
  | 2048 => (execute_MOVA_ZA_MZ2_1 2048 n nreg offset v)
  | _ => (pure ())

def decode_MOVA_ZA_MZ4_1 (Rv : (BitVec 2)) (Zn : (BitVec 3)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat off3)
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_MOVA_ZA_MZ4_1 128 n nreg offset v)
  | 256 => (execute_MOVA_ZA_MZ4_1 256 n nreg offset v)
  | 512 => (execute_MOVA_ZA_MZ4_1 512 n nreg offset v)
  | 1024 => (execute_MOVA_ZA_MZ4_1 1024 n nreg offset v)
  | 2048 => (execute_MOVA_ZA_MZ4_1 2048 n nreg offset v)
  | _ => (pure ())

def decode_MOVA_MZ2_ZA_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 8
  let d := (BitVec.toNat (Zd +++ 0#1))
  let n := 0
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_MZ2_ZA_B1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_MZ2_ZA_B1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_MZ2_ZA_B1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_MZ2_ZA_B1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_MZ2_ZA_B1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_MZ2_ZA_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 1)) (off2 : (BitVec 2)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 16
  let d := (BitVec.toNat (Zd +++ 0#1))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_MZ2_ZA_H1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_MZ2_ZA_H1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_MZ2_ZA_H1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_MZ2_ZA_H1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_MZ2_ZA_H1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_MZ2_ZA_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 2)) (o1 : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 32
  let d := (BitVec.toNat (Zd +++ 0#1))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat (o1 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_MZ2_ZA_W1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_MZ2_ZA_W1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_MZ2_ZA_W1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_MZ2_ZA_W1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_MZ2_ZA_W1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_MZ2_ZA_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 64
  let d := (BitVec.toNat (Zd +++ 0#1))
  let n := (BitVec.toNat ZAn)
  let offset := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_MZ2_ZA_D1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_MZ2_ZA_D1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_MZ2_ZA_D1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_MZ2_ZA_D1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_MZ2_ZA_D1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_MZ4_ZA_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (off2 : (BitVec 2)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 8
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let n := 0
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_MZ4_ZA_B1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_MZ4_ZA_B1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_MZ4_ZA_B1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_MZ4_ZA_B1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_MZ4_ZA_B1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_MZ4_ZA_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 1)) (o1 : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 16
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_MZ4_ZA_H1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_MZ4_ZA_H1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_MZ4_ZA_H1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_MZ4_ZA_H1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_MZ4_ZA_H1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_MZ4_ZA_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 2)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 32
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let n := (BitVec.toNat ZAn)
  let offset := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_MZ4_ZA_W1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_MZ4_ZA_W1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_MZ4_ZA_W1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_MZ4_ZA_W1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_MZ4_ZA_W1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_MZ4_ZA_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 64
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let n := (BitVec.toNat ZAn)
  let offset := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVA_MZ4_ZA_D1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVA_MZ4_ZA_D1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVA_MZ4_ZA_D1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVA_MZ4_ZA_D1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVA_MZ4_ZA_D1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVA_MZ_ZA2_1 (Rv : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat off3)
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_MOVA_MZ_ZA2_1 128 d nreg offset v)
  | 256 => (execute_MOVA_MZ_ZA2_1 256 d nreg offset v)
  | 512 => (execute_MOVA_MZ_ZA2_1 512 d nreg offset v)
  | 1024 => (execute_MOVA_MZ_ZA2_1 1024 d nreg offset v)
  | 2048 => (execute_MOVA_MZ_ZA2_1 2048 d nreg offset v)
  | _ => (pure ())

def decode_MOVA_MZ_ZA4_1 (Rv : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat off3)
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_MOVA_MZ_ZA4_1 128 d nreg offset v)
  | 256 => (execute_MOVA_MZ_ZA4_1 256 d nreg offset v)
  | 512 => (execute_MOVA_MZ_ZA4_1 512 d nreg offset v)
  | 1024 => (execute_MOVA_MZ_ZA4_1 1024 d nreg offset v)
  | 2048 => (execute_MOVA_MZ_ZA4_1 2048 d nreg offset v)
  | _ => (pure ())

def decode_LD1B_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 8
  match VL with
  | 128 => (execute_LD1B_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_LD1B_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_LD1B_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_LD1B_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LD1B_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LD1H_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 16
  match VL with
  | 128 => (execute_LD1H_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_LD1H_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_LD1H_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_LD1H_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LD1H_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LD1W_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 32
  match VL with
  | 128 => (execute_LD1W_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_LD1W_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_LD1W_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_LD1W_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LD1W_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LD1D_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 64
  match VL with
  | 128 => (execute_LD1D_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_LD1D_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_LD1D_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_LD1D_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LD1D_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LD1B_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 8
  match VL with
  | 128 => (execute_LD1B_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_LD1B_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_LD1B_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_LD1B_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LD1B_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LD1H_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 16
  match VL with
  | 128 => (execute_LD1H_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_LD1H_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_LD1H_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_LD1H_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LD1H_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LD1W_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 32
  match VL with
  | 128 => (execute_LD1W_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_LD1W_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_LD1W_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_LD1W_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LD1W_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LD1D_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 64
  match VL with
  | 128 => (execute_LD1D_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_LD1D_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_LD1D_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_LD1D_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LD1D_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LDNT1B_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 8
  match VL with
  | 128 => (execute_LDNT1B_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_LDNT1B_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_LDNT1B_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_LDNT1B_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LDNT1B_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LDNT1H_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 16
  match VL with
  | 128 => (execute_LDNT1H_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_LDNT1H_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_LDNT1H_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_LDNT1H_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LDNT1H_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LDNT1W_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 32
  match VL with
  | 128 => (execute_LDNT1W_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_LDNT1W_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_LDNT1W_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_LDNT1W_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LDNT1W_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LDNT1D_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 64
  match VL with
  | 128 => (execute_LDNT1D_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_LDNT1D_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_LDNT1D_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_LDNT1D_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LDNT1D_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LDNT1B_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 8
  match VL with
  | 128 => (execute_LDNT1B_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_LDNT1B_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_LDNT1B_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_LDNT1B_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LDNT1B_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LDNT1H_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 16
  match VL with
  | 128 => (execute_LDNT1H_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_LDNT1H_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_LDNT1H_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_LDNT1H_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LDNT1H_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LDNT1W_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 32
  match VL with
  | 128 => (execute_LDNT1W_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_LDNT1W_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_LDNT1W_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_LDNT1W_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LDNT1W_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LDNT1D_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 64
  match VL with
  | 128 => (execute_LDNT1D_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_LDNT1D_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_LDNT1D_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_LDNT1D_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_LDNT1D_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_ST1B_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 8
  match VL with
  | 128 => (execute_ST1B_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_ST1B_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_ST1B_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_ST1B_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_ST1B_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_ST1H_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 16
  match VL with
  | 128 => (execute_ST1H_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_ST1H_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_ST1H_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_ST1H_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_ST1H_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_ST1W_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 32
  match VL with
  | 128 => (execute_ST1W_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_ST1W_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_ST1W_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_ST1W_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_ST1W_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_ST1D_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 64
  match VL with
  | 128 => (execute_ST1D_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_ST1D_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_ST1D_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_ST1D_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_ST1D_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_ST1B_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 8
  match VL with
  | 128 => (execute_ST1B_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_ST1B_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_ST1B_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_ST1B_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_ST1B_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_ST1H_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 16
  match VL with
  | 128 => (execute_ST1H_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_ST1H_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_ST1H_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_ST1H_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_ST1H_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_ST1W_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 32
  match VL with
  | 128 => (execute_ST1W_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_ST1W_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_ST1W_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_ST1W_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_ST1W_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_ST1D_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 64
  match VL with
  | 128 => (execute_ST1D_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_ST1D_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_ST1D_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_ST1D_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_ST1D_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_STNT1B_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 8
  match VL with
  | 128 => (execute_STNT1B_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_STNT1B_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_STNT1B_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_STNT1B_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_STNT1B_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_STNT1H_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 16
  match VL with
  | 128 => (execute_STNT1H_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_STNT1H_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_STNT1H_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_STNT1H_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_STNT1H_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_STNT1W_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 32
  match VL with
  | 128 => (execute_STNT1W_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_STNT1W_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_STNT1W_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_STNT1W_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_STNT1W_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_STNT1D_MZx_P_BR_2x8 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 64
  match VL with
  | 128 => (execute_STNT1D_MZx_P_BR_2x8 128 esize g m n nreg t tstride)
  | 256 => (execute_STNT1D_MZx_P_BR_2x8 256 esize g m n nreg t tstride)
  | 512 => (execute_STNT1D_MZx_P_BR_2x8 512 esize g m n nreg t tstride)
  | 1024 => (execute_STNT1D_MZx_P_BR_2x8 1024 esize g m n nreg t tstride)
  | 2048 => (execute_STNT1D_MZx_P_BR_2x8 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_STNT1B_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 8
  match VL with
  | 128 => (execute_STNT1B_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_STNT1B_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_STNT1B_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_STNT1B_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_STNT1B_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_STNT1H_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 16
  match VL with
  | 128 => (execute_STNT1H_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_STNT1H_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_STNT1H_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_STNT1H_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_STNT1H_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_STNT1W_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 32
  match VL with
  | 128 => (execute_STNT1W_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_STNT1W_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_STNT1W_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_STNT1W_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_STNT1W_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_STNT1D_MZx_P_BR_4x4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 64
  match VL with
  | 128 => (execute_STNT1D_MZx_P_BR_4x4 128 esize g m n nreg t tstride)
  | 256 => (execute_STNT1D_MZx_P_BR_4x4 256 esize g m n nreg t tstride)
  | 512 => (execute_STNT1D_MZx_P_BR_4x4 512 esize g m n nreg t tstride)
  | 1024 => (execute_STNT1D_MZx_P_BR_4x4 1024 esize g m n nreg t tstride)
  | 2048 => (execute_STNT1D_MZx_P_BR_4x4 2048 esize g m n nreg t tstride)
  | _ => (pure ())

def decode_LD1B_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1B_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_LD1B_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_LD1B_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LD1B_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LD1B_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LD1H_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1H_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_LD1H_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_LD1H_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LD1H_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LD1H_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LD1W_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1W_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_LD1W_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_LD1W_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LD1W_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LD1W_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LD1D_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1D_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_LD1D_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_LD1D_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LD1D_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LD1D_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LDNT1B_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1B_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_LDNT1B_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_LDNT1B_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LDNT1B_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LDNT1B_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LDNT1H_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1H_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_LDNT1H_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_LDNT1H_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LDNT1H_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LDNT1H_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LDNT1W_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1W_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_LDNT1W_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_LDNT1W_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LDNT1W_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LDNT1W_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LDNT1D_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1D_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_LDNT1D_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_LDNT1D_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LDNT1D_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LDNT1D_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LD1B_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1B_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_LD1B_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_LD1B_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LD1B_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LD1B_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LD1H_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1H_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_LD1H_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_LD1H_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LD1H_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LD1H_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LD1W_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1W_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_LD1W_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_LD1W_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LD1W_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LD1W_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LD1D_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1D_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_LD1D_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_LD1D_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LD1D_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LD1D_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LDNT1B_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1B_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_LDNT1B_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_LDNT1B_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LDNT1B_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LDNT1B_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LDNT1H_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1H_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_LDNT1H_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_LDNT1H_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LDNT1H_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LDNT1H_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LDNT1W_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1W_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_LDNT1W_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_LDNT1W_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LDNT1W_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LDNT1W_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_LDNT1D_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1D_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_LDNT1D_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_LDNT1D_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_LDNT1D_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_LDNT1D_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_ST1B_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1B_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_ST1B_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_ST1B_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_ST1B_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_ST1B_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_ST1H_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1H_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_ST1H_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_ST1H_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_ST1H_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_ST1H_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_ST1W_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1W_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_ST1W_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_ST1W_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_ST1W_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_ST1W_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_ST1D_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1D_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_ST1D_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_ST1D_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_ST1D_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_ST1D_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_ST1B_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1B_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_ST1B_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_ST1B_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_ST1B_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_ST1B_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_ST1H_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1H_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_ST1H_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_ST1H_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_ST1H_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_ST1H_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_ST1W_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1W_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_ST1W_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_ST1W_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_ST1W_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_ST1W_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_ST1D_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1D_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_ST1D_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_ST1D_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_ST1D_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_ST1D_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_STNT1B_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1B_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_STNT1B_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_STNT1B_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_STNT1B_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_STNT1B_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_STNT1H_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1H_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_STNT1H_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_STNT1H_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_STNT1H_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_STNT1H_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_STNT1W_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1W_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_STNT1W_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_STNT1W_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_STNT1W_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_STNT1W_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_STNT1D_MZx_P_BI_2x8 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let tstride := 8
  let t := (BitVec.toNat ((T +++ 0#1) +++ Zt))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1D_MZx_P_BI_2x8 128 esize g n nreg offset t tstride)
  | 256 => (execute_STNT1D_MZx_P_BI_2x8 256 esize g n nreg offset t tstride)
  | 512 => (execute_STNT1D_MZx_P_BI_2x8 512 esize g n nreg offset t tstride)
  | 1024 => (execute_STNT1D_MZx_P_BI_2x8 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_STNT1D_MZx_P_BI_2x8 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_STNT1B_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1B_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_STNT1B_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_STNT1B_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_STNT1B_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_STNT1B_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_STNT1H_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1H_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_STNT1H_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_STNT1H_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_STNT1H_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_STNT1H_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_STNT1W_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1W_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_STNT1W_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_STNT1W_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_STNT1W_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_STNT1W_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_STNT1D_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let tstride := 4
  let t := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1D_MZx_P_BI_4x4 128 esize g n nreg offset t tstride)
  | 256 => (execute_STNT1D_MZx_P_BI_4x4 256 esize g n nreg offset t tstride)
  | 512 => (execute_STNT1D_MZx_P_BI_4x4 512 esize g n nreg offset t tstride)
  | 1024 => (execute_STNT1D_MZx_P_BI_4x4 1024 esize g n nreg offset t tstride)
  | 2048 => (execute_STNT1D_MZx_P_BI_4x4 2048 esize g n nreg offset t tstride)
  | _ => (pure ())

def decode_FADD_ZA_ZW_2x2 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_FADD_ZA_ZW_2x2 128 esize m nreg offset v)
  | 256 => (execute_FADD_ZA_ZW_2x2 256 esize m nreg offset v)
  | 512 => (execute_FADD_ZA_ZW_2x2 512 esize m nreg offset v)
  | 1024 => (execute_FADD_ZA_ZW_2x2 1024 esize m nreg offset v)
  | 2048 => (execute_FADD_ZA_ZW_2x2 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_FSUB_ZA_ZW_2x2 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_FSUB_ZA_ZW_2x2 128 esize m nreg offset v)
  | 256 => (execute_FSUB_ZA_ZW_2x2 256 esize m nreg offset v)
  | 512 => (execute_FSUB_ZA_ZW_2x2 512 esize m nreg offset v)
  | 1024 => (execute_FSUB_ZA_ZW_2x2 1024 esize m nreg offset v)
  | 2048 => (execute_FSUB_ZA_ZW_2x2 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_FADD_ZA_ZW_4x4 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_FADD_ZA_ZW_4x4 128 esize m nreg offset v)
  | 256 => (execute_FADD_ZA_ZW_4x4 256 esize m nreg offset v)
  | 512 => (execute_FADD_ZA_ZW_4x4 512 esize m nreg offset v)
  | 1024 => (execute_FADD_ZA_ZW_4x4 1024 esize m nreg offset v)
  | 2048 => (execute_FADD_ZA_ZW_4x4 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_FSUB_ZA_ZW_4x4 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_FSUB_ZA_ZW_4x4 128 esize m nreg offset v)
  | 256 => (execute_FSUB_ZA_ZW_4x4 256 esize m nreg offset v)
  | 512 => (execute_FSUB_ZA_ZW_4x4 512 esize m nreg offset v)
  | 1024 => (execute_FSUB_ZA_ZW_4x4 1024 esize m nreg offset v)
  | 2048 => (execute_FSUB_ZA_ZW_4x4 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_FMLA_ZA_ZZW_2x2 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZW_2x2 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZW_2x2 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZW_2x2 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZW_2x2 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_FMLS_ZA_ZZW_2x2 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZW_2x2 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZW_2x2 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZW_2x2 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZW_2x2 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_FMLA_ZA_ZZV_2x1 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZV_2x1 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZV_2x1 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZV_2x1 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZV_2x1 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_FMLS_ZA_ZZV_2x1 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZV_2x1 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZV_2x1 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZV_2x1 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZV_2x1 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_FMLA_ZA_ZZW_4x4 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZW_4x4 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZW_4x4 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZW_4x4 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZW_4x4 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_FMLS_ZA_ZZW_4x4 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZW_4x4 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZW_4x4 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZW_4x4 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZW_4x4 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZV_4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_FMLA_ZA_ZZV_4x1 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZV_4x1 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZV_4x1 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZV_4x1 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZV_4x1 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZV_4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEF64F64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_FMLS_ZA_ZZV_4x1 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZV_4x1 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZV_4x1 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZV_4x1 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZV_4x1 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_FMLA_ZA_ZZi_S2xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZi_S2xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZi_S2xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZi_S2xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZi_S2xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_FMLS_ZA_ZZi_S2xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZi_S2xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZi_S2xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZi_S2xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZi_S2xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i1 : (BitVec 1)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEF64F64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i1)
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_FMLA_ZA_ZZi_D2xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZi_D2xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZi_D2xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZi_D2xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZi_D2xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i1 : (BitVec 1)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEF64F64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i1)
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_FMLS_ZA_ZZi_D2xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZi_D2xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZi_D2xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZi_D2xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZi_D2xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_FMLA_ZA_ZZi_S4xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZi_S4xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZi_S4xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZi_S4xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZi_S4xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_FMLS_ZA_ZZi_S4xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZi_S4xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZi_S4xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZi_S4xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZi_S4xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZi_D4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i1 : (BitVec 1)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEF64F64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i1)
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_FMLA_ZA_ZZi_D4xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZi_D4xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZi_D4xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZi_D4xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZi_D4xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZi_D4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i1 : (BitVec 1)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEF64F64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i1)
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_FMLS_ZA_ZZi_D4xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZi_D4xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZi_D4xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZi_D4xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZi_D4xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFDOT_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_BFDOT_ZA_ZZW_2x2 128 m n nreg offset v)
  | 256 => (execute_BFDOT_ZA_ZZW_2x2 256 m n nreg offset v)
  | 512 => (execute_BFDOT_ZA_ZZW_2x2 512 m n nreg offset v)
  | 1024 => (execute_BFDOT_ZA_ZZW_2x2 1024 m n nreg offset v)
  | 2048 => (execute_BFDOT_ZA_ZZW_2x2 2048 m n nreg offset v)
  | _ => (pure ())

def decode_BFDOT_ZA_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_BFDOT_ZA_ZZV_2x1 128 m n nreg offset v)
  | 256 => (execute_BFDOT_ZA_ZZV_2x1 256 m n nreg offset v)
  | 512 => (execute_BFDOT_ZA_ZZV_2x1 512 m n nreg offset v)
  | 1024 => (execute_BFDOT_ZA_ZZV_2x1 1024 m n nreg offset v)
  | 2048 => (execute_BFDOT_ZA_ZZV_2x1 2048 m n nreg offset v)
  | _ => (pure ())

def decode_FDOT_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_FDOT_ZA_ZZW_2x2 128 m n nreg offset v)
  | 256 => (execute_FDOT_ZA_ZZW_2x2 256 m n nreg offset v)
  | 512 => (execute_FDOT_ZA_ZZW_2x2 512 m n nreg offset v)
  | 1024 => (execute_FDOT_ZA_ZZW_2x2 1024 m n nreg offset v)
  | 2048 => (execute_FDOT_ZA_ZZW_2x2 2048 m n nreg offset v)
  | _ => (pure ())

def decode_FDOT_ZA_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_FDOT_ZA_ZZV_2x1 128 m n nreg offset v)
  | 256 => (execute_FDOT_ZA_ZZV_2x1 256 m n nreg offset v)
  | 512 => (execute_FDOT_ZA_ZZV_2x1 512 m n nreg offset v)
  | 1024 => (execute_FDOT_ZA_ZZV_2x1 1024 m n nreg offset v)
  | 2048 => (execute_FDOT_ZA_ZZV_2x1 2048 m n nreg offset v)
  | _ => (pure ())

def decode_BFDOT_ZA_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_BFDOT_ZA_ZZW_4x4 128 m n nreg offset v)
  | 256 => (execute_BFDOT_ZA_ZZW_4x4 256 m n nreg offset v)
  | 512 => (execute_BFDOT_ZA_ZZW_4x4 512 m n nreg offset v)
  | 1024 => (execute_BFDOT_ZA_ZZW_4x4 1024 m n nreg offset v)
  | 2048 => (execute_BFDOT_ZA_ZZW_4x4 2048 m n nreg offset v)
  | _ => (pure ())

def decode_BFDOT_ZA_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_BFDOT_ZA_ZZV_4x1 128 m n nreg offset v)
  | 256 => (execute_BFDOT_ZA_ZZV_4x1 256 m n nreg offset v)
  | 512 => (execute_BFDOT_ZA_ZZV_4x1 512 m n nreg offset v)
  | 1024 => (execute_BFDOT_ZA_ZZV_4x1 1024 m n nreg offset v)
  | 2048 => (execute_BFDOT_ZA_ZZV_4x1 2048 m n nreg offset v)
  | _ => (pure ())

def decode_FDOT_ZA_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_FDOT_ZA_ZZW_4x4 128 m n nreg offset v)
  | 256 => (execute_FDOT_ZA_ZZW_4x4 256 m n nreg offset v)
  | 512 => (execute_FDOT_ZA_ZZW_4x4 512 m n nreg offset v)
  | 1024 => (execute_FDOT_ZA_ZZW_4x4 1024 m n nreg offset v)
  | 2048 => (execute_FDOT_ZA_ZZW_4x4 2048 m n nreg offset v)
  | _ => (pure ())

def decode_FDOT_ZA_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_FDOT_ZA_ZZV_4x1 128 m n nreg offset v)
  | 256 => (execute_FDOT_ZA_ZZV_4x1 256 m n nreg offset v)
  | 512 => (execute_FDOT_ZA_ZZV_4x1 512 m n nreg offset v)
  | 1024 => (execute_FDOT_ZA_ZZV_4x1 1024 m n nreg offset v)
  | 2048 => (execute_FDOT_ZA_ZZV_4x1 2048 m n nreg offset v)
  | _ => (pure ())

def decode_BFDOT_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 2
  match VL with
  | 128 => (execute_BFDOT_ZA_ZZi_2xi 128 index m n nreg offset v)
  | 256 => (execute_BFDOT_ZA_ZZi_2xi 256 index m n nreg offset v)
  | 512 => (execute_BFDOT_ZA_ZZi_2xi 512 index m n nreg offset v)
  | 1024 => (execute_BFDOT_ZA_ZZi_2xi 1024 index m n nreg offset v)
  | 2048 => (execute_BFDOT_ZA_ZZi_2xi 2048 index m n nreg offset v)
  | _ => (pure ())

def decode_BFDOT_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 4
  match VL with
  | 128 => (execute_BFDOT_ZA_ZZi_4xi 128 index m n nreg offset v)
  | 256 => (execute_BFDOT_ZA_ZZi_4xi 256 index m n nreg offset v)
  | 512 => (execute_BFDOT_ZA_ZZi_4xi 512 index m n nreg offset v)
  | 1024 => (execute_BFDOT_ZA_ZZi_4xi 1024 index m n nreg offset v)
  | 2048 => (execute_BFDOT_ZA_ZZi_4xi 2048 index m n nreg offset v)
  | _ => (pure ())

def decode_FDOT_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 2
  match VL with
  | 128 => (execute_FDOT_ZA_ZZi_2xi 128 index m n nreg offset v)
  | 256 => (execute_FDOT_ZA_ZZi_2xi 256 index m n nreg offset v)
  | 512 => (execute_FDOT_ZA_ZZi_2xi 512 index m n nreg offset v)
  | 1024 => (execute_FDOT_ZA_ZZi_2xi 1024 index m n nreg offset v)
  | 2048 => (execute_FDOT_ZA_ZZi_2xi 2048 index m n nreg offset v)
  | _ => (pure ())

def decode_FDOT_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 4
  match VL with
  | 128 => (execute_FDOT_ZA_ZZi_4xi 128 index m n nreg offset v)
  | 256 => (execute_FDOT_ZA_ZZi_4xi 256 index m n nreg offset v)
  | 512 => (execute_FDOT_ZA_ZZi_4xi 512 index m n nreg offset v)
  | 1024 => (execute_FDOT_ZA_ZZi_4xi 1024 index m n nreg offset v)
  | 2048 => (execute_FDOT_ZA_ZZi_4xi 2048 index m n nreg offset v)
  | _ => (pure ())

def decode_BFVDOT_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_BFVDOT_ZA_ZZi_2xi 128 index m n offset v)
  | 256 => (execute_BFVDOT_ZA_ZZi_2xi 256 index m n offset v)
  | 512 => (execute_BFVDOT_ZA_ZZi_2xi 512 index m n offset v)
  | 1024 => (execute_BFVDOT_ZA_ZZi_2xi 1024 index m n offset v)
  | 2048 => (execute_BFVDOT_ZA_ZZi_2xi 2048 index m n offset v)
  | _ => (pure ())

def decode_FVDOT_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_FVDOT_ZA_ZZi_2xi 128 index m n offset v)
  | 256 => (execute_FVDOT_ZA_ZZi_2xi 256 index m n offset v)
  | 512 => (execute_FVDOT_ZA_ZZi_2xi 512 index m n offset v)
  | 1024 => (execute_FVDOT_ZA_ZZi_2xi 1024 index m n offset v)
  | 2048 => (execute_FVDOT_ZA_ZZi_2xi 2048 index m n offset v)
  | _ => (pure ())

def decode_BFMLAL_ZA_ZZV_1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let sub_op : Bool := false
  let nreg := 1
  match VL with
  | 128 => (execute_BFMLAL_ZA_ZZV_1 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLAL_ZA_ZZV_1 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLAL_ZA_ZZV_1 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLAL_ZA_ZZV_1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLAL_ZA_ZZV_1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLAL_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLAL_ZA_ZZW_2x2 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLAL_ZA_ZZW_2x2 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLAL_ZA_ZZW_2x2 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLAL_ZA_ZZW_2x2 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLAL_ZA_ZZW_2x2 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLAL_ZA_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLAL_ZA_ZZV_2x1 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLAL_ZA_ZZV_2x1 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLAL_ZA_ZZV_2x1 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLAL_ZA_ZZV_2x1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLAL_ZA_ZZV_2x1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLAL_ZA_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLAL_ZA_ZZW_4x4 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLAL_ZA_ZZW_4x4 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLAL_ZA_ZZW_4x4 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLAL_ZA_ZZW_4x4 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLAL_ZA_ZZW_4x4 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLAL_ZA_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLAL_ZA_ZZV_4x1 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLAL_ZA_ZZV_4x1 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLAL_ZA_ZZV_4x1 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLAL_ZA_ZZV_4x1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLAL_ZA_ZZV_4x1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLSL_ZA_ZZV_1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let sub_op : Bool := true
  let nreg := 1
  match VL with
  | 128 => (execute_BFMLSL_ZA_ZZV_1 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLSL_ZA_ZZV_1 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLSL_ZA_ZZV_1 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLSL_ZA_ZZV_1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLSL_ZA_ZZV_1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLSL_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLSL_ZA_ZZW_2x2 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLSL_ZA_ZZW_2x2 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLSL_ZA_ZZW_2x2 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLSL_ZA_ZZW_2x2 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLSL_ZA_ZZW_2x2 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLSL_ZA_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLSL_ZA_ZZV_2x1 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLSL_ZA_ZZV_2x1 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLSL_ZA_ZZV_2x1 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLSL_ZA_ZZV_2x1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLSL_ZA_ZZV_2x1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLSL_ZA_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLSL_ZA_ZZW_4x4 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLSL_ZA_ZZW_4x4 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLSL_ZA_ZZW_4x4 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLSL_ZA_ZZW_4x4 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLSL_ZA_ZZW_4x4 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLSL_ZA_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLSL_ZA_ZZV_4x1 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLSL_ZA_ZZV_4x1 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLSL_ZA_ZZV_4x1 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLSL_ZA_ZZV_4x1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLSL_ZA_ZZV_4x1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLAL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg := 1
  match VL with
  | 128 => (execute_BFMLAL_ZA_ZZi_1 128 index m n nreg offset sub_op v)
  | 256 => (execute_BFMLAL_ZA_ZZi_1 256 index m n nreg offset sub_op v)
  | 512 => (execute_BFMLAL_ZA_ZZi_1 512 index m n nreg offset sub_op v)
  | 1024 => (execute_BFMLAL_ZA_ZZi_1 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_BFMLAL_ZA_ZZi_1 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLAL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLAL_ZA_ZZi_2xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_BFMLAL_ZA_ZZi_2xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_BFMLAL_ZA_ZZi_2xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_BFMLAL_ZA_ZZi_2xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_BFMLAL_ZA_ZZi_2xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLAL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLAL_ZA_ZZi_4xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_BFMLAL_ZA_ZZi_4xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_BFMLAL_ZA_ZZi_4xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_BFMLAL_ZA_ZZi_4xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_BFMLAL_ZA_ZZi_4xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLSL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg := 1
  match VL with
  | 128 => (execute_BFMLSL_ZA_ZZi_1 128 index m n nreg offset sub_op v)
  | 256 => (execute_BFMLSL_ZA_ZZi_1 256 index m n nreg offset sub_op v)
  | 512 => (execute_BFMLSL_ZA_ZZi_1 512 index m n nreg offset sub_op v)
  | 1024 => (execute_BFMLSL_ZA_ZZi_1 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_BFMLSL_ZA_ZZi_1 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLSL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLSL_ZA_ZZi_2xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_BFMLSL_ZA_ZZi_2xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_BFMLSL_ZA_ZZi_2xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_BFMLSL_ZA_ZZi_2xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_BFMLSL_ZA_ZZi_2xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLSL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLSL_ZA_ZZi_4xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_BFMLSL_ZA_ZZi_4xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_BFMLSL_ZA_ZZi_4xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_BFMLSL_ZA_ZZi_4xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_BFMLSL_ZA_ZZi_4xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLAL_ZA_ZZV_1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let sub_op : Bool := false
  let nreg := 1
  match VL with
  | 128 => (execute_FMLAL_ZA_ZZV_1 128 m n nreg offset sub_op v)
  | 256 => (execute_FMLAL_ZA_ZZV_1 256 m n nreg offset sub_op v)
  | 512 => (execute_FMLAL_ZA_ZZV_1 512 m n nreg offset sub_op v)
  | 1024 => (execute_FMLAL_ZA_ZZV_1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_FMLAL_ZA_ZZV_1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLAL_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_FMLAL_ZA_ZZW_2x2 128 m n nreg offset sub_op v)
  | 256 => (execute_FMLAL_ZA_ZZW_2x2 256 m n nreg offset sub_op v)
  | 512 => (execute_FMLAL_ZA_ZZW_2x2 512 m n nreg offset sub_op v)
  | 1024 => (execute_FMLAL_ZA_ZZW_2x2 1024 m n nreg offset sub_op v)
  | 2048 => (execute_FMLAL_ZA_ZZW_2x2 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLAL_ZA_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_FMLAL_ZA_ZZV_2x1 128 m n nreg offset sub_op v)
  | 256 => (execute_FMLAL_ZA_ZZV_2x1 256 m n nreg offset sub_op v)
  | 512 => (execute_FMLAL_ZA_ZZV_2x1 512 m n nreg offset sub_op v)
  | 1024 => (execute_FMLAL_ZA_ZZV_2x1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_FMLAL_ZA_ZZV_2x1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLAL_ZA_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_FMLAL_ZA_ZZW_4x4 128 m n nreg offset sub_op v)
  | 256 => (execute_FMLAL_ZA_ZZW_4x4 256 m n nreg offset sub_op v)
  | 512 => (execute_FMLAL_ZA_ZZW_4x4 512 m n nreg offset sub_op v)
  | 1024 => (execute_FMLAL_ZA_ZZW_4x4 1024 m n nreg offset sub_op v)
  | 2048 => (execute_FMLAL_ZA_ZZW_4x4 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLAL_ZA_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_FMLAL_ZA_ZZV_4x1 128 m n nreg offset sub_op v)
  | 256 => (execute_FMLAL_ZA_ZZV_4x1 256 m n nreg offset sub_op v)
  | 512 => (execute_FMLAL_ZA_ZZV_4x1 512 m n nreg offset sub_op v)
  | 1024 => (execute_FMLAL_ZA_ZZV_4x1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_FMLAL_ZA_ZZV_4x1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLAL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg := 1
  match VL with
  | 128 => (execute_FMLAL_ZA_ZZi_1 128 index m n nreg offset sub_op v)
  | 256 => (execute_FMLAL_ZA_ZZi_1 256 index m n nreg offset sub_op v)
  | 512 => (execute_FMLAL_ZA_ZZi_1 512 index m n nreg offset sub_op v)
  | 1024 => (execute_FMLAL_ZA_ZZi_1 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_FMLAL_ZA_ZZi_1 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLAL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_FMLAL_ZA_ZZi_2xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_FMLAL_ZA_ZZi_2xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_FMLAL_ZA_ZZi_2xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_FMLAL_ZA_ZZi_2xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_FMLAL_ZA_ZZi_2xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLAL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_FMLAL_ZA_ZZi_4xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_FMLAL_ZA_ZZi_4xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_FMLAL_ZA_ZZi_4xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_FMLAL_ZA_ZZi_4xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_FMLAL_ZA_ZZi_4xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLSL_ZA_ZZV_1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let sub_op : Bool := true
  let nreg := 1
  match VL with
  | 128 => (execute_FMLSL_ZA_ZZV_1 128 m n nreg offset sub_op v)
  | 256 => (execute_FMLSL_ZA_ZZV_1 256 m n nreg offset sub_op v)
  | 512 => (execute_FMLSL_ZA_ZZV_1 512 m n nreg offset sub_op v)
  | 1024 => (execute_FMLSL_ZA_ZZV_1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_FMLSL_ZA_ZZV_1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLSL_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_FMLSL_ZA_ZZW_2x2 128 m n nreg offset sub_op v)
  | 256 => (execute_FMLSL_ZA_ZZW_2x2 256 m n nreg offset sub_op v)
  | 512 => (execute_FMLSL_ZA_ZZW_2x2 512 m n nreg offset sub_op v)
  | 1024 => (execute_FMLSL_ZA_ZZW_2x2 1024 m n nreg offset sub_op v)
  | 2048 => (execute_FMLSL_ZA_ZZW_2x2 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLSL_ZA_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_FMLSL_ZA_ZZV_2x1 128 m n nreg offset sub_op v)
  | 256 => (execute_FMLSL_ZA_ZZV_2x1 256 m n nreg offset sub_op v)
  | 512 => (execute_FMLSL_ZA_ZZV_2x1 512 m n nreg offset sub_op v)
  | 1024 => (execute_FMLSL_ZA_ZZV_2x1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_FMLSL_ZA_ZZV_2x1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLSL_ZA_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_FMLSL_ZA_ZZW_4x4 128 m n nreg offset sub_op v)
  | 256 => (execute_FMLSL_ZA_ZZW_4x4 256 m n nreg offset sub_op v)
  | 512 => (execute_FMLSL_ZA_ZZW_4x4 512 m n nreg offset sub_op v)
  | 1024 => (execute_FMLSL_ZA_ZZW_4x4 1024 m n nreg offset sub_op v)
  | 2048 => (execute_FMLSL_ZA_ZZW_4x4 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLSL_ZA_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_FMLSL_ZA_ZZV_4x1 128 m n nreg offset sub_op v)
  | 256 => (execute_FMLSL_ZA_ZZV_4x1 256 m n nreg offset sub_op v)
  | 512 => (execute_FMLSL_ZA_ZZV_4x1 512 m n nreg offset sub_op v)
  | 1024 => (execute_FMLSL_ZA_ZZV_4x1 1024 m n nreg offset sub_op v)
  | 2048 => (execute_FMLSL_ZA_ZZV_4x1 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLSL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg := 1
  match VL with
  | 128 => (execute_FMLSL_ZA_ZZi_1 128 index m n nreg offset sub_op v)
  | 256 => (execute_FMLSL_ZA_ZZi_1 256 index m n nreg offset sub_op v)
  | 512 => (execute_FMLSL_ZA_ZZi_1 512 index m n nreg offset sub_op v)
  | 1024 => (execute_FMLSL_ZA_ZZi_1 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_FMLSL_ZA_ZZi_1 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLSL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_FMLSL_ZA_ZZi_2xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_FMLSL_ZA_ZZi_2xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_FMLSL_ZA_ZZi_2xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_FMLSL_ZA_ZZi_2xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_FMLSL_ZA_ZZi_2xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLSL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_FMLSL_ZA_ZZi_4xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_FMLSL_ZA_ZZi_4xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_FMLSL_ZA_ZZi_4xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_FMLSL_ZA_ZZi_4xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_FMLSL_ZA_ZZi_4xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMAX_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_FMAX_MZ_ZZW_2x2 128 dn esize m nreg)
  | 256 => (execute_FMAX_MZ_ZZW_2x2 256 dn esize m nreg)
  | 512 => (execute_FMAX_MZ_ZZW_2x2 512 dn esize m nreg)
  | 1024 => (execute_FMAX_MZ_ZZW_2x2 1024 dn esize m nreg)
  | 2048 => (execute_FMAX_MZ_ZZW_2x2 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMAX_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_FMAX_MZ_ZZV_2x1 128 dn esize m nreg)
  | 256 => (execute_FMAX_MZ_ZZV_2x1 256 dn esize m nreg)
  | 512 => (execute_FMAX_MZ_ZZV_2x1 512 dn esize m nreg)
  | 1024 => (execute_FMAX_MZ_ZZV_2x1 1024 dn esize m nreg)
  | 2048 => (execute_FMAX_MZ_ZZV_2x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMIN_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_FMIN_MZ_ZZW_2x2 128 dn esize m nreg)
  | 256 => (execute_FMIN_MZ_ZZW_2x2 256 dn esize m nreg)
  | 512 => (execute_FMIN_MZ_ZZW_2x2 512 dn esize m nreg)
  | 1024 => (execute_FMIN_MZ_ZZW_2x2 1024 dn esize m nreg)
  | 2048 => (execute_FMIN_MZ_ZZW_2x2 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMIN_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_FMIN_MZ_ZZV_2x1 128 dn esize m nreg)
  | 256 => (execute_FMIN_MZ_ZZV_2x1 256 dn esize m nreg)
  | 512 => (execute_FMIN_MZ_ZZV_2x1 512 dn esize m nreg)
  | 1024 => (execute_FMIN_MZ_ZZV_2x1 1024 dn esize m nreg)
  | 2048 => (execute_FMIN_MZ_ZZV_2x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMAX_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_FMAX_MZ_ZZW_4x4 128 dn esize m nreg)
  | 256 => (execute_FMAX_MZ_ZZW_4x4 256 dn esize m nreg)
  | 512 => (execute_FMAX_MZ_ZZW_4x4 512 dn esize m nreg)
  | 1024 => (execute_FMAX_MZ_ZZW_4x4 1024 dn esize m nreg)
  | 2048 => (execute_FMAX_MZ_ZZW_4x4 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMAX_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_FMAX_MZ_ZZV_4x1 128 dn esize m nreg)
  | 256 => (execute_FMAX_MZ_ZZV_4x1 256 dn esize m nreg)
  | 512 => (execute_FMAX_MZ_ZZV_4x1 512 dn esize m nreg)
  | 1024 => (execute_FMAX_MZ_ZZV_4x1 1024 dn esize m nreg)
  | 2048 => (execute_FMAX_MZ_ZZV_4x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMIN_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_FMIN_MZ_ZZW_4x4 128 dn esize m nreg)
  | 256 => (execute_FMIN_MZ_ZZW_4x4 256 dn esize m nreg)
  | 512 => (execute_FMIN_MZ_ZZW_4x4 512 dn esize m nreg)
  | 1024 => (execute_FMIN_MZ_ZZW_4x4 1024 dn esize m nreg)
  | 2048 => (execute_FMIN_MZ_ZZW_4x4 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMIN_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_FMIN_MZ_ZZV_4x1 128 dn esize m nreg)
  | 256 => (execute_FMIN_MZ_ZZV_4x1 256 dn esize m nreg)
  | 512 => (execute_FMIN_MZ_ZZV_4x1 512 dn esize m nreg)
  | 1024 => (execute_FMIN_MZ_ZZV_4x1 1024 dn esize m nreg)
  | 2048 => (execute_FMIN_MZ_ZZV_4x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMAXNM_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_FMAXNM_MZ_ZZW_2x2 128 dn esize m nreg)
  | 256 => (execute_FMAXNM_MZ_ZZW_2x2 256 dn esize m nreg)
  | 512 => (execute_FMAXNM_MZ_ZZW_2x2 512 dn esize m nreg)
  | 1024 => (execute_FMAXNM_MZ_ZZW_2x2 1024 dn esize m nreg)
  | 2048 => (execute_FMAXNM_MZ_ZZW_2x2 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMAXNM_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_FMAXNM_MZ_ZZV_2x1 128 dn esize m nreg)
  | 256 => (execute_FMAXNM_MZ_ZZV_2x1 256 dn esize m nreg)
  | 512 => (execute_FMAXNM_MZ_ZZV_2x1 512 dn esize m nreg)
  | 1024 => (execute_FMAXNM_MZ_ZZV_2x1 1024 dn esize m nreg)
  | 2048 => (execute_FMAXNM_MZ_ZZV_2x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMINNM_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_FMINNM_MZ_ZZW_2x2 128 dn esize m nreg)
  | 256 => (execute_FMINNM_MZ_ZZW_2x2 256 dn esize m nreg)
  | 512 => (execute_FMINNM_MZ_ZZW_2x2 512 dn esize m nreg)
  | 1024 => (execute_FMINNM_MZ_ZZW_2x2 1024 dn esize m nreg)
  | 2048 => (execute_FMINNM_MZ_ZZW_2x2 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMINNM_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_FMINNM_MZ_ZZV_2x1 128 dn esize m nreg)
  | 256 => (execute_FMINNM_MZ_ZZV_2x1 256 dn esize m nreg)
  | 512 => (execute_FMINNM_MZ_ZZV_2x1 512 dn esize m nreg)
  | 1024 => (execute_FMINNM_MZ_ZZV_2x1 1024 dn esize m nreg)
  | 2048 => (execute_FMINNM_MZ_ZZV_2x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMAXNM_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_FMAXNM_MZ_ZZW_4x4 128 dn esize m nreg)
  | 256 => (execute_FMAXNM_MZ_ZZW_4x4 256 dn esize m nreg)
  | 512 => (execute_FMAXNM_MZ_ZZW_4x4 512 dn esize m nreg)
  | 1024 => (execute_FMAXNM_MZ_ZZW_4x4 1024 dn esize m nreg)
  | 2048 => (execute_FMAXNM_MZ_ZZW_4x4 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMAXNM_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_FMAXNM_MZ_ZZV_4x1 128 dn esize m nreg)
  | 256 => (execute_FMAXNM_MZ_ZZV_4x1 256 dn esize m nreg)
  | 512 => (execute_FMAXNM_MZ_ZZV_4x1 512 dn esize m nreg)
  | 1024 => (execute_FMAXNM_MZ_ZZV_4x1 1024 dn esize m nreg)
  | 2048 => (execute_FMAXNM_MZ_ZZV_4x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMINNM_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_FMINNM_MZ_ZZW_4x4 128 dn esize m nreg)
  | 256 => (execute_FMINNM_MZ_ZZW_4x4 256 dn esize m nreg)
  | 512 => (execute_FMINNM_MZ_ZZW_4x4 512 dn esize m nreg)
  | 1024 => (execute_FMINNM_MZ_ZZW_4x4 1024 dn esize m nreg)
  | 2048 => (execute_FMINNM_MZ_ZZW_4x4 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FMINNM_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_FMINNM_MZ_ZZV_4x1 128 dn esize m nreg)
  | 256 => (execute_FMINNM_MZ_ZZV_4x1 256 dn esize m nreg)
  | 512 => (execute_FMINNM_MZ_ZZV_4x1 512 dn esize m nreg)
  | 1024 => (execute_FMINNM_MZ_ZZV_4x1 1024 dn esize m nreg)
  | 2048 => (execute_FMINNM_MZ_ZZV_4x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_FCLAMP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_FCLAMP_MZ_ZZ_2 128 d esize m n nreg)
  | 256 => (execute_FCLAMP_MZ_ZZ_2 256 d esize m n nreg)
  | 512 => (execute_FCLAMP_MZ_ZZ_2 512 d esize m n nreg)
  | 1024 => (execute_FCLAMP_MZ_ZZ_2 1024 d esize m n nreg)
  | 2048 => (execute_FCLAMP_MZ_ZZ_2 2048 d esize m n nreg)
  | _ => (pure ())

def decode_FCLAMP_MZ_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_FCLAMP_MZ_ZZ_4 128 d esize m n nreg)
  | 256 => (execute_FCLAMP_MZ_ZZ_4 256 d esize m n nreg)
  | 512 => (execute_FCLAMP_MZ_ZZ_4 512 d esize m n nreg)
  | 1024 => (execute_FCLAMP_MZ_ZZ_4 1024 d esize m n nreg)
  | 2048 => (execute_FCLAMP_MZ_ZZ_4 2048 d esize m n nreg)
  | _ => (pure ())

def decode_BFCVT_Z_MZ2__ (Zn : (BitVec 4)) (N : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BFCVT_Z_MZ2__ 128 d n)
  | 256 => (execute_BFCVT_Z_MZ2__ 256 d n)
  | 512 => (execute_BFCVT_Z_MZ2__ 512 d n)
  | 1024 => (execute_BFCVT_Z_MZ2__ 1024 d n)
  | 2048 => (execute_BFCVT_Z_MZ2__ 2048 d n)
  | _ => (pure ())

def decode_FCVT_Z_MZ2__ (Zn : (BitVec 4)) (N : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FCVT_Z_MZ2__ 128 d n)
  | 256 => (execute_FCVT_Z_MZ2__ 256 d n)
  | 512 => (execute_FCVT_Z_MZ2__ 512 d n)
  | 1024 => (execute_FCVT_Z_MZ2__ 1024 d n)
  | 2048 => (execute_FCVT_Z_MZ2__ 2048 d n)
  | _ => (pure ())

def decode_BFCVTN_Z_MZ2__ (Zn : (BitVec 4)) (N : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BFCVTN_Z_MZ2__ 128 d n)
  | 256 => (execute_BFCVTN_Z_MZ2__ 256 d n)
  | 512 => (execute_BFCVTN_Z_MZ2__ 512 d n)
  | 1024 => (execute_BFCVTN_Z_MZ2__ 1024 d n)
  | 2048 => (execute_BFCVTN_Z_MZ2__ 2048 d n)
  | _ => (pure ())

def decode_FCVTN_Z_MZ2__ (Zn : (BitVec 4)) (N : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FCVTN_Z_MZ2__ 128 d n)
  | 256 => (execute_FCVTN_Z_MZ2__ 256 d n)
  | 512 => (execute_FCVTN_Z_MZ2__ 512 d n)
  | 1024 => (execute_FCVTN_Z_MZ2__ 1024 d n)
  | 2048 => (execute_FCVTN_Z_MZ2__ 2048 d n)
  | _ => (pure ())

def decode_FCVTZU_MZ_Z_2 (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZU_MZ_Z_2 128 d n nreg rounding is_unsigned)
  | 256 => (execute_FCVTZU_MZ_Z_2 256 d n nreg rounding is_unsigned)
  | 512 => (execute_FCVTZU_MZ_Z_2 512 d n nreg rounding is_unsigned)
  | 1024 => (execute_FCVTZU_MZ_Z_2 1024 d n nreg rounding is_unsigned)
  | 2048 => (execute_FCVTZU_MZ_Z_2 2048 d n nreg rounding is_unsigned)
  | _ => (pure ())

def decode_FCVTZU_MZ_Z_4 (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZU_MZ_Z_4 128 d n nreg rounding is_unsigned)
  | 256 => (execute_FCVTZU_MZ_Z_4 256 d n nreg rounding is_unsigned)
  | 512 => (execute_FCVTZU_MZ_Z_4 512 d n nreg rounding is_unsigned)
  | 1024 => (execute_FCVTZU_MZ_Z_4 1024 d n nreg rounding is_unsigned)
  | 2048 => (execute_FCVTZU_MZ_Z_4 2048 d n nreg rounding is_unsigned)
  | _ => (pure ())

def decode_FCVTZS_MZ_Z_2 (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZS_MZ_Z_2 128 d n nreg rounding is_unsigned)
  | 256 => (execute_FCVTZS_MZ_Z_2 256 d n nreg rounding is_unsigned)
  | 512 => (execute_FCVTZS_MZ_Z_2 512 d n nreg rounding is_unsigned)
  | 1024 => (execute_FCVTZS_MZ_Z_2 1024 d n nreg rounding is_unsigned)
  | 2048 => (execute_FCVTZS_MZ_Z_2 2048 d n nreg rounding is_unsigned)
  | _ => (pure ())

def decode_FCVTZS_MZ_Z_4 (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZS_MZ_Z_4 128 d n nreg rounding is_unsigned)
  | 256 => (execute_FCVTZS_MZ_Z_4 256 d n nreg rounding is_unsigned)
  | 512 => (execute_FCVTZS_MZ_Z_4 512 d n nreg rounding is_unsigned)
  | 1024 => (execute_FCVTZS_MZ_Z_4 1024 d n nreg rounding is_unsigned)
  | 2048 => (execute_FCVTZS_MZ_Z_4 2048 d n nreg rounding is_unsigned)
  | _ => (pure ())

def decode_UCVTF_MZ_Z_2 (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  let is_unsigned : Bool := true
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_UCVTF_MZ_Z_2 128 d n nreg rounding is_unsigned)
  | 256 => (execute_UCVTF_MZ_Z_2 256 d n nreg rounding is_unsigned)
  | 512 => (execute_UCVTF_MZ_Z_2 512 d n nreg rounding is_unsigned)
  | 1024 => (execute_UCVTF_MZ_Z_2 1024 d n nreg rounding is_unsigned)
  | 2048 => (execute_UCVTF_MZ_Z_2 2048 d n nreg rounding is_unsigned)
  | _ => (pure ())

def decode_UCVTF_MZ_Z_4 (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  let is_unsigned : Bool := true
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_UCVTF_MZ_Z_4 128 d n nreg rounding is_unsigned)
  | 256 => (execute_UCVTF_MZ_Z_4 256 d n nreg rounding is_unsigned)
  | 512 => (execute_UCVTF_MZ_Z_4 512 d n nreg rounding is_unsigned)
  | 1024 => (execute_UCVTF_MZ_Z_4 1024 d n nreg rounding is_unsigned)
  | 2048 => (execute_UCVTF_MZ_Z_4 2048 d n nreg rounding is_unsigned)
  | _ => (pure ())

def decode_SCVTF_MZ_Z_2 (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  let is_unsigned : Bool := false
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_SCVTF_MZ_Z_2 128 d n nreg rounding is_unsigned)
  | 256 => (execute_SCVTF_MZ_Z_2 256 d n nreg rounding is_unsigned)
  | 512 => (execute_SCVTF_MZ_Z_2 512 d n nreg rounding is_unsigned)
  | 1024 => (execute_SCVTF_MZ_Z_2 1024 d n nreg rounding is_unsigned)
  | 2048 => (execute_SCVTF_MZ_Z_2 2048 d n nreg rounding is_unsigned)
  | _ => (pure ())

def decode_SCVTF_MZ_Z_4 (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  let is_unsigned : Bool := false
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_SCVTF_MZ_Z_4 128 d n nreg rounding is_unsigned)
  | 256 => (execute_SCVTF_MZ_Z_4 256 d n nreg rounding is_unsigned)
  | 512 => (execute_SCVTF_MZ_Z_4 512 d n nreg rounding is_unsigned)
  | 1024 => (execute_SCVTF_MZ_Z_4 1024 d n nreg rounding is_unsigned)
  | 2048 => (execute_SCVTF_MZ_Z_4 2048 d n nreg rounding is_unsigned)
  | _ => (pure ())

def decode_FRINTA_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_TIEAWAY
  match VL with
  | 128 => (execute_FRINTA_MZ_Z_2 128 d exact n nreg rounding)
  | 256 => (execute_FRINTA_MZ_Z_2 256 d exact n nreg rounding)
  | 512 => (execute_FRINTA_MZ_Z_2 512 d exact n nreg rounding)
  | 1024 => (execute_FRINTA_MZ_Z_2 1024 d exact n nreg rounding)
  | 2048 => (execute_FRINTA_MZ_Z_2 2048 d exact n nreg rounding)
  | _ => (pure ())

def decode_FRINTM_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_NEGINF
  match VL with
  | 128 => (execute_FRINTM_MZ_Z_2 128 d exact n nreg rounding)
  | 256 => (execute_FRINTM_MZ_Z_2 256 d exact n nreg rounding)
  | 512 => (execute_FRINTM_MZ_Z_2 512 d exact n nreg rounding)
  | 1024 => (execute_FRINTM_MZ_Z_2 1024 d exact n nreg rounding)
  | 2048 => (execute_FRINTM_MZ_Z_2 2048 d exact n nreg rounding)
  | _ => (pure ())

def decode_FRINTN_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_TIEEVEN
  match VL with
  | 128 => (execute_FRINTN_MZ_Z_2 128 d exact n nreg rounding)
  | 256 => (execute_FRINTN_MZ_Z_2 256 d exact n nreg rounding)
  | 512 => (execute_FRINTN_MZ_Z_2 512 d exact n nreg rounding)
  | 1024 => (execute_FRINTN_MZ_Z_2 1024 d exact n nreg rounding)
  | 2048 => (execute_FRINTN_MZ_Z_2 2048 d exact n nreg rounding)
  | _ => (pure ())

def decode_FRINTP_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_POSINF
  match VL with
  | 128 => (execute_FRINTP_MZ_Z_2 128 d exact n nreg rounding)
  | 256 => (execute_FRINTP_MZ_Z_2 256 d exact n nreg rounding)
  | 512 => (execute_FRINTP_MZ_Z_2 512 d exact n nreg rounding)
  | 1024 => (execute_FRINTP_MZ_Z_2 1024 d exact n nreg rounding)
  | 2048 => (execute_FRINTP_MZ_Z_2 2048 d exact n nreg rounding)
  | _ => (pure ())

def decode_FRINTA_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_TIEAWAY
  match VL with
  | 128 => (execute_FRINTA_MZ_Z_4 128 d exact n nreg rounding)
  | 256 => (execute_FRINTA_MZ_Z_4 256 d exact n nreg rounding)
  | 512 => (execute_FRINTA_MZ_Z_4 512 d exact n nreg rounding)
  | 1024 => (execute_FRINTA_MZ_Z_4 1024 d exact n nreg rounding)
  | 2048 => (execute_FRINTA_MZ_Z_4 2048 d exact n nreg rounding)
  | _ => (pure ())

def decode_FRINTM_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_NEGINF
  match VL with
  | 128 => (execute_FRINTM_MZ_Z_4 128 d exact n nreg rounding)
  | 256 => (execute_FRINTM_MZ_Z_4 256 d exact n nreg rounding)
  | 512 => (execute_FRINTM_MZ_Z_4 512 d exact n nreg rounding)
  | 1024 => (execute_FRINTM_MZ_Z_4 1024 d exact n nreg rounding)
  | 2048 => (execute_FRINTM_MZ_Z_4 2048 d exact n nreg rounding)
  | _ => (pure ())

def decode_FRINTN_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_TIEEVEN
  match VL with
  | 128 => (execute_FRINTN_MZ_Z_4 128 d exact n nreg rounding)
  | 256 => (execute_FRINTN_MZ_Z_4 256 d exact n nreg rounding)
  | 512 => (execute_FRINTN_MZ_Z_4 512 d exact n nreg rounding)
  | 1024 => (execute_FRINTN_MZ_Z_4 1024 d exact n nreg rounding)
  | 2048 => (execute_FRINTN_MZ_Z_4 2048 d exact n nreg rounding)
  | _ => (pure ())

def decode_FRINTP_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_POSINF
  match VL with
  | 128 => (execute_FRINTP_MZ_Z_4 128 d exact n nreg rounding)
  | 256 => (execute_FRINTP_MZ_Z_4 256 d exact n nreg rounding)
  | 512 => (execute_FRINTP_MZ_Z_4 512 d exact n nreg rounding)
  | 1024 => (execute_FRINTP_MZ_Z_4 1024 d exact n nreg rounding)
  | 2048 => (execute_FRINTP_MZ_Z_4 2048 d exact n nreg rounding)
  | _ => (pure ())

def decode_ADD_ZA_ZW_2x2 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_ADD_ZA_ZW_2x2 128 esize m nreg offset v)
  | 256 => (execute_ADD_ZA_ZW_2x2 256 esize m nreg offset v)
  | 512 => (execute_ADD_ZA_ZW_2x2 512 esize m nreg offset v)
  | 1024 => (execute_ADD_ZA_ZW_2x2 1024 esize m nreg offset v)
  | 2048 => (execute_ADD_ZA_ZW_2x2 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_SUB_ZA_ZW_2x2 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_SUB_ZA_ZW_2x2 128 esize m nreg offset v)
  | 256 => (execute_SUB_ZA_ZW_2x2 256 esize m nreg offset v)
  | 512 => (execute_SUB_ZA_ZW_2x2 512 esize m nreg offset v)
  | 1024 => (execute_SUB_ZA_ZW_2x2 1024 esize m nreg offset v)
  | 2048 => (execute_SUB_ZA_ZW_2x2 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_ADD_ZA_ZW_4x4 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_ADD_ZA_ZW_4x4 128 esize m nreg offset v)
  | 256 => (execute_ADD_ZA_ZW_4x4 256 esize m nreg offset v)
  | 512 => (execute_ADD_ZA_ZW_4x4 512 esize m nreg offset v)
  | 1024 => (execute_ADD_ZA_ZW_4x4 1024 esize m nreg offset v)
  | 2048 => (execute_ADD_ZA_ZW_4x4 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_SUB_ZA_ZW_4x4 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_SUB_ZA_ZW_4x4 128 esize m nreg offset v)
  | 256 => (execute_SUB_ZA_ZW_4x4 256 esize m nreg offset v)
  | 512 => (execute_SUB_ZA_ZW_4x4 512 esize m nreg offset v)
  | 1024 => (execute_SUB_ZA_ZW_4x4 1024 esize m nreg offset v)
  | 2048 => (execute_SUB_ZA_ZW_4x4 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_ADD_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_ADD_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_ADD_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_ADD_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_ADD_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_ADD_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SUB_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_SUB_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_SUB_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_SUB_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_SUB_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_SUB_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_ADD_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_ADD_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_ADD_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_ADD_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_ADD_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_ADD_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SUB_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_SUB_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_SUB_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_SUB_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_SUB_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SUB_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_ADD_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_ADD_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_ADD_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_ADD_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_ADD_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_ADD_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SUB_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_SUB_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_SUB_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_SUB_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_SUB_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_SUB_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_ADD_ZA_ZZV_4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_ADD_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_ADD_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_ADD_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_ADD_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_ADD_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SUB_ZA_ZZV_4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_SUB_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_SUB_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_SUB_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_SUB_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SUB_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_UDOT_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_UDOT_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_UDOT_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_UDOT_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_UDOT_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_SDOT_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_SDOT_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_SDOT_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_SDOT_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_SDOT_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_USDOT_ZA_ZZW_S2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_USDOT_ZA_ZZW_S2x2 128 esize m n nreg offset v)
  | 256 => (execute_USDOT_ZA_ZZW_S2x2 256 esize m n nreg offset v)
  | 512 => (execute_USDOT_ZA_ZZW_S2x2 512 esize m n nreg offset v)
  | 1024 => (execute_USDOT_ZA_ZZW_S2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_USDOT_ZA_ZZW_S2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_UDOT_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_UDOT_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_UDOT_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_UDOT_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UDOT_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_SDOT_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_SDOT_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_SDOT_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_SDOT_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SDOT_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_USDOT_ZA_ZZV_S2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_USDOT_ZA_ZZV_S2x1 128 esize m n nreg offset v)
  | 256 => (execute_USDOT_ZA_ZZV_S2x1 256 esize m n nreg offset v)
  | 512 => (execute_USDOT_ZA_ZZV_S2x1 512 esize m n nreg offset v)
  | 1024 => (execute_USDOT_ZA_ZZV_S2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_USDOT_ZA_ZZV_S2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SUDOT_ZA_ZZV_S2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_SUDOT_ZA_ZZV_S2x1 128 esize m n nreg offset v)
  | 256 => (execute_SUDOT_ZA_ZZV_S2x1 256 esize m n nreg offset v)
  | 512 => (execute_SUDOT_ZA_ZZV_S2x1 512 esize m n nreg offset v)
  | 1024 => (execute_SUDOT_ZA_ZZV_S2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SUDOT_ZA_ZZV_S2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_UDOT_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_UDOT_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_UDOT_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_UDOT_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_UDOT_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_SDOT_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_SDOT_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_SDOT_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_SDOT_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_SDOT_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_USDOT_ZA_ZZW_S4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_USDOT_ZA_ZZW_S4x4 128 esize m n nreg offset v)
  | 256 => (execute_USDOT_ZA_ZZW_S4x4 256 esize m n nreg offset v)
  | 512 => (execute_USDOT_ZA_ZZW_S4x4 512 esize m n nreg offset v)
  | 1024 => (execute_USDOT_ZA_ZZW_S4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_USDOT_ZA_ZZW_S4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA_ZZV_4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_UDOT_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_UDOT_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_UDOT_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_UDOT_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UDOT_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA_ZZV_4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_SDOT_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_SDOT_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_SDOT_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_SDOT_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SDOT_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_USDOT_ZA_ZZV_S4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_USDOT_ZA_ZZV_S4x1 128 esize m n nreg offset v)
  | 256 => (execute_USDOT_ZA_ZZV_S4x1 256 esize m n nreg offset v)
  | 512 => (execute_USDOT_ZA_ZZV_S4x1 512 esize m n nreg offset v)
  | 1024 => (execute_USDOT_ZA_ZZV_S4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_USDOT_ZA_ZZV_S4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SUDOT_ZA_ZZV_S4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_SUDOT_ZA_ZZV_S4x1 128 esize m n nreg offset v)
  | 256 => (execute_SUDOT_ZA_ZZV_S4x1 256 esize m n nreg offset v)
  | 512 => (execute_SUDOT_ZA_ZZV_S4x1 512 esize m n nreg offset v)
  | 1024 => (execute_SUDOT_ZA_ZZV_S4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SUDOT_ZA_ZZV_S4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 2
  match VL with
  | 128 => (execute_UDOT_ZA_ZZi_S2xi 128 esize index m n nreg offset v)
  | 256 => (execute_UDOT_ZA_ZZi_S2xi 256 esize index m n nreg offset v)
  | 512 => (execute_UDOT_ZA_ZZi_S2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UDOT_ZA_ZZi_S2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UDOT_ZA_ZZi_S2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 2
  match VL with
  | 128 => (execute_SDOT_ZA_ZZi_S2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SDOT_ZA_ZZi_S2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SDOT_ZA_ZZi_S2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SDOT_ZA_ZZi_S2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SDOT_ZA_ZZi_S2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_USDOT_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 2
  match VL with
  | 128 => (execute_USDOT_ZA_ZZi_S2xi 128 esize index m n nreg offset v)
  | 256 => (execute_USDOT_ZA_ZZi_S2xi 256 esize index m n nreg offset v)
  | 512 => (execute_USDOT_ZA_ZZi_S2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_USDOT_ZA_ZZi_S2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_USDOT_ZA_ZZi_S2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SUDOT_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 2
  match VL with
  | 128 => (execute_SUDOT_ZA_ZZi_S2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SUDOT_ZA_ZZi_S2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SUDOT_ZA_ZZi_S2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SUDOT_ZA_ZZi_S2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SUDOT_ZA_ZZi_S2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i1 : (BitVec 1)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i1)
  let nreg := 2
  match VL with
  | 128 => (execute_UDOT_ZA_ZZi_D2xi 128 esize index m n nreg offset v)
  | 256 => (execute_UDOT_ZA_ZZi_D2xi 256 esize index m n nreg offset v)
  | 512 => (execute_UDOT_ZA_ZZi_D2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UDOT_ZA_ZZi_D2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UDOT_ZA_ZZi_D2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i1 : (BitVec 1)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i1)
  let nreg := 2
  match VL with
  | 128 => (execute_SDOT_ZA_ZZi_D2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SDOT_ZA_ZZi_D2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SDOT_ZA_ZZi_D2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SDOT_ZA_ZZi_D2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SDOT_ZA_ZZi_D2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 4
  match VL with
  | 128 => (execute_UDOT_ZA_ZZi_S4xi 128 esize index m n nreg offset v)
  | 256 => (execute_UDOT_ZA_ZZi_S4xi 256 esize index m n nreg offset v)
  | 512 => (execute_UDOT_ZA_ZZi_S4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UDOT_ZA_ZZi_S4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UDOT_ZA_ZZi_S4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 4
  match VL with
  | 128 => (execute_SDOT_ZA_ZZi_S4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SDOT_ZA_ZZi_S4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SDOT_ZA_ZZi_S4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SDOT_ZA_ZZi_S4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SDOT_ZA_ZZi_S4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_USDOT_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 4
  match VL with
  | 128 => (execute_USDOT_ZA_ZZi_S4xi 128 esize index m n nreg offset v)
  | 256 => (execute_USDOT_ZA_ZZi_S4xi 256 esize index m n nreg offset v)
  | 512 => (execute_USDOT_ZA_ZZi_S4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_USDOT_ZA_ZZi_S4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_USDOT_ZA_ZZi_S4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SUDOT_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 4
  match VL with
  | 128 => (execute_SUDOT_ZA_ZZi_S4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SUDOT_ZA_ZZi_S4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SUDOT_ZA_ZZi_S4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SUDOT_ZA_ZZi_S4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SUDOT_ZA_ZZi_S4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA_ZZi_D4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i1 : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i1)
  let nreg := 4
  match VL with
  | 128 => (execute_UDOT_ZA_ZZi_D4xi 128 esize index m n nreg offset v)
  | 256 => (execute_UDOT_ZA_ZZi_D4xi 256 esize index m n nreg offset v)
  | 512 => (execute_UDOT_ZA_ZZi_D4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UDOT_ZA_ZZi_D4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UDOT_ZA_ZZi_D4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA_ZZi_D4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i1 : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i1)
  let nreg := 4
  match VL with
  | 128 => (execute_SDOT_ZA_ZZi_D4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SDOT_ZA_ZZi_D4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SDOT_ZA_ZZi_D4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SDOT_ZA_ZZi_D4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SDOT_ZA_ZZi_D4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UVDOT_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_UVDOT_ZA_ZZi_S4xi 128 esize index m n offset v)
  | 256 => (execute_UVDOT_ZA_ZZi_S4xi 256 esize index m n offset v)
  | 512 => (execute_UVDOT_ZA_ZZi_S4xi 512 esize index m n offset v)
  | 1024 => (execute_UVDOT_ZA_ZZi_S4xi 1024 esize index m n offset v)
  | 2048 => (execute_UVDOT_ZA_ZZi_S4xi 2048 esize index m n offset v)
  | _ => (pure ())

def decode_SVDOT_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_SVDOT_ZA_ZZi_S4xi 128 esize index m n offset v)
  | 256 => (execute_SVDOT_ZA_ZZi_S4xi 256 esize index m n offset v)
  | 512 => (execute_SVDOT_ZA_ZZi_S4xi 512 esize index m n offset v)
  | 1024 => (execute_SVDOT_ZA_ZZi_S4xi 1024 esize index m n offset v)
  | 2048 => (execute_SVDOT_ZA_ZZi_S4xi 2048 esize index m n offset v)
  | _ => (pure ())

def decode_USVDOT_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_USVDOT_ZA_ZZi_S4xi 128 esize index m n offset v)
  | 256 => (execute_USVDOT_ZA_ZZi_S4xi 256 esize index m n offset v)
  | 512 => (execute_USVDOT_ZA_ZZi_S4xi 512 esize index m n offset v)
  | 1024 => (execute_USVDOT_ZA_ZZi_S4xi 1024 esize index m n offset v)
  | 2048 => (execute_USVDOT_ZA_ZZi_S4xi 2048 esize index m n offset v)
  | _ => (pure ())

def decode_SUVDOT_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_SUVDOT_ZA_ZZi_S4xi 128 esize index m n offset v)
  | 256 => (execute_SUVDOT_ZA_ZZi_S4xi 256 esize index m n offset v)
  | 512 => (execute_SUVDOT_ZA_ZZi_S4xi 512 esize index m n offset v)
  | 1024 => (execute_SUVDOT_ZA_ZZi_S4xi 1024 esize index m n offset v)
  | 2048 => (execute_SUVDOT_ZA_ZZi_S4xi 2048 esize index m n offset v)
  | _ => (pure ())

def decode_UVDOT_ZA_ZZi_D4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i1 : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i1)
  match VL with
  | 128 => (execute_UVDOT_ZA_ZZi_D4xi 128 esize index m n offset v)
  | 256 => (execute_UVDOT_ZA_ZZi_D4xi 256 esize index m n offset v)
  | 512 => (execute_UVDOT_ZA_ZZi_D4xi 512 esize index m n offset v)
  | 1024 => (execute_UVDOT_ZA_ZZi_D4xi 1024 esize index m n offset v)
  | 2048 => (execute_UVDOT_ZA_ZZi_D4xi 2048 esize index m n offset v)
  | _ => (pure ())

def decode_SVDOT_ZA_ZZi_D4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i1 : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 64
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i1)
  match VL with
  | 128 => (execute_SVDOT_ZA_ZZi_D4xi 128 esize index m n offset v)
  | 256 => (execute_SVDOT_ZA_ZZi_D4xi 256 esize index m n offset v)
  | 512 => (execute_SVDOT_ZA_ZZi_D4xi 512 esize index m n offset v)
  | 1024 => (execute_SVDOT_ZA_ZZi_D4xi 1024 esize index m n offset v)
  | 2048 => (execute_SVDOT_ZA_ZZi_D4xi 2048 esize index m n offset v)
  | _ => (pure ())

def decode_UDOT_ZA32_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_UDOT_ZA32_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_UDOT_ZA32_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_UDOT_ZA32_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_UDOT_ZA32_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_UDOT_ZA32_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA32_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_SDOT_ZA32_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_SDOT_ZA32_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_SDOT_ZA32_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_SDOT_ZA32_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_SDOT_ZA32_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA32_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_UDOT_ZA32_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_UDOT_ZA32_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_UDOT_ZA32_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_UDOT_ZA32_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UDOT_ZA32_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA32_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_SDOT_ZA32_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_SDOT_ZA32_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_SDOT_ZA32_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_SDOT_ZA32_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SDOT_ZA32_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA32_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_UDOT_ZA32_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_UDOT_ZA32_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_UDOT_ZA32_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_UDOT_ZA32_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_UDOT_ZA32_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA32_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_SDOT_ZA32_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_SDOT_ZA32_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_SDOT_ZA32_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_SDOT_ZA32_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_SDOT_ZA32_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA32_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_UDOT_ZA32_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_UDOT_ZA32_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_UDOT_ZA32_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_UDOT_ZA32_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UDOT_ZA32_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA32_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_SDOT_ZA32_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_SDOT_ZA32_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_SDOT_ZA32_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_SDOT_ZA32_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SDOT_ZA32_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA32_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 2
  match VL with
  | 128 => (execute_UDOT_ZA32_ZZi_2xi 128 esize index m n nreg offset v)
  | 256 => (execute_UDOT_ZA32_ZZi_2xi 256 esize index m n nreg offset v)
  | 512 => (execute_UDOT_ZA32_ZZi_2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UDOT_ZA32_ZZi_2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UDOT_ZA32_ZZi_2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA32_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 2
  match VL with
  | 128 => (execute_SDOT_ZA32_ZZi_2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SDOT_ZA32_ZZi_2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SDOT_ZA32_ZZi_2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SDOT_ZA32_ZZi_2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SDOT_ZA32_ZZi_2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UDOT_ZA32_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 4
  match VL with
  | 128 => (execute_UDOT_ZA32_ZZi_4xi 128 esize index m n nreg offset v)
  | 256 => (execute_UDOT_ZA32_ZZi_4xi 256 esize index m n nreg offset v)
  | 512 => (execute_UDOT_ZA32_ZZi_4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UDOT_ZA32_ZZi_4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UDOT_ZA32_ZZi_4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SDOT_ZA32_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  let nreg := 4
  match VL with
  | 128 => (execute_SDOT_ZA32_ZZi_4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SDOT_ZA32_ZZi_4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SDOT_ZA32_ZZi_4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SDOT_ZA32_ZZi_4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SDOT_ZA32_ZZi_4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UVDOT_ZA32_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_UVDOT_ZA32_ZZi_2xi 128 esize index m n offset v)
  | 256 => (execute_UVDOT_ZA32_ZZi_2xi 256 esize index m n offset v)
  | 512 => (execute_UVDOT_ZA32_ZZi_2xi 512 esize index m n offset v)
  | 1024 => (execute_UVDOT_ZA32_ZZi_2xi 1024 esize index m n offset v)
  | 2048 => (execute_UVDOT_ZA32_ZZi_2xi 2048 esize index m n offset v)
  | _ => (pure ())

def decode_SVDOT_ZA32_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 32
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_SVDOT_ZA32_ZZi_2xi 128 esize index m n offset v)
  | 256 => (execute_SVDOT_ZA32_ZZi_2xi 256 esize index m n offset v)
  | 512 => (execute_SVDOT_ZA32_ZZi_2xi 512 esize index m n offset v)
  | 1024 => (execute_SVDOT_ZA32_ZZi_2xi 1024 esize index m n offset v)
  | 2048 => (execute_SVDOT_ZA32_ZZi_2xi 2048 esize index m n offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZV_1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let nreg := 1
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZV_1 128 esize m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZV_1 256 esize m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZV_1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZV_1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZV_1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZV_1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let nreg := 1
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZV_1 128 esize m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZV_1 256 esize m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZV_1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZV_1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZV_1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZV_1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let nreg := 1
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZV_1 128 esize m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZV_1 256 esize m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZV_1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZV_1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZV_1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZV_1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let nreg := 1
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZV_1 128 esize m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZV_1 256 esize m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZV_1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZV_1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZV_1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_USMLALL_ZA_ZZV_S (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let nreg := 1
  match VL with
  | 128 => (execute_USMLALL_ZA_ZZV_S 128 esize m n nreg offset v)
  | 256 => (execute_USMLALL_ZA_ZZV_S 256 esize m n nreg offset v)
  | 512 => (execute_USMLALL_ZA_ZZV_S 512 esize m n nreg offset v)
  | 1024 => (execute_USMLALL_ZA_ZZV_S 1024 esize m n nreg offset v)
  | 2048 => (execute_USMLALL_ZA_ZZV_S 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_USMLALL_ZA_ZZW_S2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_USMLALL_ZA_ZZW_S2x2 128 esize m n nreg offset v)
  | 256 => (execute_USMLALL_ZA_ZZW_S2x2 256 esize m n nreg offset v)
  | 512 => (execute_USMLALL_ZA_ZZW_S2x2 512 esize m n nreg offset v)
  | 1024 => (execute_USMLALL_ZA_ZZW_S2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_USMLALL_ZA_ZZW_S2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZV_2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_USMLALL_ZA_ZZV_S2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_USMLALL_ZA_ZZV_S2x1 128 esize m n nreg offset v)
  | 256 => (execute_USMLALL_ZA_ZZV_S2x1 256 esize m n nreg offset v)
  | 512 => (execute_USMLALL_ZA_ZZV_S2x1 512 esize m n nreg offset v)
  | 1024 => (execute_USMLALL_ZA_ZZV_S2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_USMLALL_ZA_ZZV_S2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SUMLALL_ZA_ZZV_S2x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 2
  match VL with
  | 128 => (execute_SUMLALL_ZA_ZZV_S2x1 128 esize m n nreg offset v)
  | 256 => (execute_SUMLALL_ZA_ZZV_S2x1 256 esize m n nreg offset v)
  | 512 => (execute_SUMLALL_ZA_ZZV_S2x1 512 esize m n nreg offset v)
  | 1024 => (execute_SUMLALL_ZA_ZZV_S2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SUMLALL_ZA_ZZV_S2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZW_4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_USMLALL_ZA_ZZW_S4x4 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_USMLALL_ZA_ZZW_S4x4 128 esize m n nreg offset v)
  | 256 => (execute_USMLALL_ZA_ZZW_S4x4 256 esize m n nreg offset v)
  | 512 => (execute_USMLALL_ZA_ZZW_S4x4 512 esize m n nreg offset v)
  | 1024 => (execute_USMLALL_ZA_ZZW_S4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_USMLALL_ZA_ZZW_S4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZV_4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZV_4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZV_4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZV_4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (sz == 1#1)) <&&> (do
       (pure (! (← (HaveSMEI16I64 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_USMLALL_ZA_ZZV_S4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_USMLALL_ZA_ZZV_S4x1 128 esize m n nreg offset v)
  | 256 => (execute_USMLALL_ZA_ZZV_S4x1 256 esize m n nreg offset v)
  | 512 => (execute_USMLALL_ZA_ZZV_S4x1 512 esize m n nreg offset v)
  | 1024 => (execute_USMLALL_ZA_ZZV_S4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_USMLALL_ZA_ZZV_S4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SUMLALL_ZA_ZZV_S4x1 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_SUMLALL_ZA_ZZV_S4x1 128 esize m n nreg offset v)
  | 256 => (execute_SUMLALL_ZA_ZZV_S4x1 256 esize m n nreg offset v)
  | 512 => (execute_SUMLALL_ZA_ZZV_S4x1 512 esize m n nreg offset v)
  | 1024 => (execute_SUMLALL_ZA_ZZV_S4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SUMLALL_ZA_ZZV_S4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZi_S (Zm : (BitVec 4)) (i4h : (BitVec 1)) (Rv : (BitVec 2)) (i4l : (BitVec 3)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 1
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZi_S 128 esize index m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZi_S 256 esize index m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZi_S 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZi_S 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZi_S 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZi_S (Zm : (BitVec 4)) (i4h : (BitVec 1)) (Rv : (BitVec 2)) (i4l : (BitVec 3)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 1
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZi_S 128 esize index m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZi_S 256 esize index m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZi_S 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZi_S 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZi_S 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZi_S (Zm : (BitVec 4)) (i4h : (BitVec 1)) (Rv : (BitVec 2)) (i4l : (BitVec 3)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 1
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZi_S 128 esize index m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZi_S 256 esize index m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZi_S 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZi_S 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZi_S 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZi_S (Zm : (BitVec 4)) (i4h : (BitVec 1)) (Rv : (BitVec 2)) (i4l : (BitVec 3)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 1
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZi_S 128 esize index m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZi_S 256 esize index m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZi_S 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZi_S 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZi_S 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_USMLALL_ZA_ZZi_S (Zm : (BitVec 4)) (i4h : (BitVec 1)) (Rv : (BitVec 2)) (i4l : (BitVec 3)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 1
  match VL with
  | 128 => (execute_USMLALL_ZA_ZZi_S 128 esize index m n nreg offset v)
  | 256 => (execute_USMLALL_ZA_ZZi_S 256 esize index m n nreg offset v)
  | 512 => (execute_USMLALL_ZA_ZZi_S 512 esize index m n nreg offset v)
  | 1024 => (execute_USMLALL_ZA_ZZi_S 1024 esize index m n nreg offset v)
  | 2048 => (execute_USMLALL_ZA_ZZi_S 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SUMLALL_ZA_ZZi_S (Zm : (BitVec 4)) (i4h : (BitVec 1)) (Rv : (BitVec 2)) (i4l : (BitVec 3)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 1
  match VL with
  | 128 => (execute_SUMLALL_ZA_ZZi_S 128 esize index m n nreg offset v)
  | 256 => (execute_SUMLALL_ZA_ZZi_S 256 esize index m n nreg offset v)
  | 512 => (execute_SUMLALL_ZA_ZZi_S 512 esize index m n nreg offset v)
  | 1024 => (execute_SUMLALL_ZA_ZZi_S 1024 esize index m n nreg offset v)
  | 2048 => (execute_SUMLALL_ZA_ZZi_S 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZi_D (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 1
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZi_D 128 esize index m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZi_D 256 esize index m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZi_D 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZi_D 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZi_D 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZi_D (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 1
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZi_D 128 esize index m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZi_D 256 esize index m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZi_D 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZi_D 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZi_D 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZi_D (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 1
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZi_D 128 esize index m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZi_D 256 esize index m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZi_D 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZi_D 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZi_D 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZi_D (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 1
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZi_D 128 esize index m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZi_D 256 esize index m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZi_D 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZi_D 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZi_D 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZi_S2xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZi_S2xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZi_S2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZi_S2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZi_S2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZi_S2xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZi_S2xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZi_S2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZi_S2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZi_S2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZi_S2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZi_S2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZi_S2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZi_S2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZi_S2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZi_S2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZi_S2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZi_S2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZi_S2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZi_S2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_USMLALL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 2
  match VL with
  | 128 => (execute_USMLALL_ZA_ZZi_S2xi 128 esize index m n nreg offset v)
  | 256 => (execute_USMLALL_ZA_ZZi_S2xi 256 esize index m n nreg offset v)
  | 512 => (execute_USMLALL_ZA_ZZi_S2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_USMLALL_ZA_ZZi_S2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_USMLALL_ZA_ZZi_S2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SUMLALL_ZA_ZZi_S2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 2
  match VL with
  | 128 => (execute_SUMLALL_ZA_ZZi_S2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SUMLALL_ZA_ZZi_S2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SUMLALL_ZA_ZZi_S2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SUMLALL_ZA_ZZi_S2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SUMLALL_ZA_ZZi_S2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZi_D2xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZi_D2xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZi_D2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZi_D2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZi_D2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZi_D2xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZi_D2xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZi_D2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZi_D2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZi_D2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZi_D2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZi_D2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZi_D2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZi_D2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZi_D2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZi_D2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZi_D2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZi_D2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZi_D2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZi_D2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZi_D2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZi_S4xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZi_S4xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZi_S4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZi_S4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZi_S4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZi_S4xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZi_S4xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZi_S4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZi_S4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZi_S4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZi_S4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZi_S4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZi_S4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZi_S4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZi_S4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZi_S4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZi_S4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZi_S4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZi_S4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZi_S4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_USMLALL_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 4
  match VL with
  | 128 => (execute_USMLALL_ZA_ZZi_S4xi 128 esize index m n nreg offset v)
  | 256 => (execute_USMLALL_ZA_ZZi_S4xi 256 esize index m n nreg offset v)
  | 512 => (execute_USMLALL_ZA_ZZi_S4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_USMLALL_ZA_ZZi_S4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_USMLALL_ZA_ZZi_S4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SUMLALL_ZA_ZZi_S4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i4h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i4l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i4h +++ i4l))
  let nreg := 4
  match VL with
  | 128 => (execute_SUMLALL_ZA_ZZi_S4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SUMLALL_ZA_ZZi_S4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SUMLALL_ZA_ZZi_S4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SUMLALL_ZA_ZZi_S4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SUMLALL_ZA_ZZi_S4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLALL_ZA_ZZi_D4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLALL_ZA_ZZi_D4xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLALL_ZA_ZZi_D4xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLALL_ZA_ZZi_D4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLALL_ZA_ZZi_D4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLALL_ZA_ZZi_D4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLSLL_ZA_ZZi_D4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLSLL_ZA_ZZi_D4xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLSLL_ZA_ZZi_D4xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLSLL_ZA_ZZi_D4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLSLL_ZA_ZZi_D4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLSLL_ZA_ZZi_D4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLALL_ZA_ZZi_D4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLALL_ZA_ZZi_D4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLALL_ZA_ZZi_D4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLALL_ZA_ZZi_D4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLALL_ZA_ZZi_D4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLALL_ZA_ZZi_D4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLSLL_ZA_ZZi_D4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (←((HaveSME2 ()) <&&> (do
         (HaveSMEI16I64 ()))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLSLL_ZA_ZZi_D4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLSLL_ZA_ZZi_D4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLSLL_ZA_ZZi_D4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLSLL_ZA_ZZi_D4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLSLL_ZA_ZZi_D4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLAL_ZA_ZZV_1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let nreg := 1
  match VL with
  | 128 => (execute_UMLAL_ZA_ZZV_1 128 esize m n nreg offset v)
  | 256 => (execute_UMLAL_ZA_ZZV_1 256 esize m n nreg offset v)
  | 512 => (execute_UMLAL_ZA_ZZV_1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLAL_ZA_ZZV_1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLAL_ZA_ZZV_1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLSL_ZA_ZZV_1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let nreg := 1
  match VL with
  | 128 => (execute_UMLSL_ZA_ZZV_1 128 esize m n nreg offset v)
  | 256 => (execute_UMLSL_ZA_ZZV_1 256 esize m n nreg offset v)
  | 512 => (execute_UMLSL_ZA_ZZV_1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLSL_ZA_ZZV_1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLSL_ZA_ZZV_1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLAL_ZA_ZZV_1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let nreg := 1
  match VL with
  | 128 => (execute_SMLAL_ZA_ZZV_1 128 esize m n nreg offset v)
  | 256 => (execute_SMLAL_ZA_ZZV_1 256 esize m n nreg offset v)
  | 512 => (execute_SMLAL_ZA_ZZV_1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLAL_ZA_ZZV_1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLAL_ZA_ZZV_1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLSL_ZA_ZZV_1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let nreg := 1
  match VL with
  | 128 => (execute_SMLSL_ZA_ZZV_1 128 esize m n nreg offset v)
  | 256 => (execute_SMLSL_ZA_ZZV_1 256 esize m n nreg offset v)
  | 512 => (execute_SMLSL_ZA_ZZV_1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLSL_ZA_ZZV_1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLSL_ZA_ZZV_1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLAL_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLAL_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_UMLAL_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_UMLAL_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_UMLAL_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLAL_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLSL_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLSL_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_UMLSL_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_UMLSL_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_UMLSL_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLSL_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLAL_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLAL_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_SMLAL_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_SMLAL_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_SMLAL_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLAL_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLSL_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLSL_ZA_ZZW_2x2 128 esize m n nreg offset v)
  | 256 => (execute_SMLSL_ZA_ZZW_2x2 256 esize m n nreg offset v)
  | 512 => (execute_SMLSL_ZA_ZZW_2x2 512 esize m n nreg offset v)
  | 1024 => (execute_SMLSL_ZA_ZZW_2x2 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLSL_ZA_ZZW_2x2 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLAL_ZA_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLAL_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_UMLAL_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_UMLAL_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLAL_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLAL_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLSL_ZA_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLSL_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_UMLSL_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_UMLSL_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLSL_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLSL_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLAL_ZA_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLAL_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_SMLAL_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_SMLAL_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLAL_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLAL_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLSL_ZA_ZZV_2x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLSL_ZA_ZZV_2x1 128 esize m n nreg offset v)
  | 256 => (execute_SMLSL_ZA_ZZV_2x1 256 esize m n nreg offset v)
  | 512 => (execute_SMLSL_ZA_ZZV_2x1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLSL_ZA_ZZV_2x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLSL_ZA_ZZV_2x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLAL_ZA_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLAL_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_UMLAL_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_UMLAL_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_UMLAL_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLAL_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLSL_ZA_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLSL_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_UMLSL_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_UMLSL_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_UMLSL_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLSL_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLAL_ZA_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLAL_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_SMLAL_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_SMLAL_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_SMLAL_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLAL_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLSL_ZA_ZZW_4x4 (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLSL_ZA_ZZW_4x4 128 esize m n nreg offset v)
  | 256 => (execute_SMLSL_ZA_ZZW_4x4 256 esize m n nreg offset v)
  | 512 => (execute_SMLSL_ZA_ZZW_4x4 512 esize m n nreg offset v)
  | 1024 => (execute_SMLSL_ZA_ZZW_4x4 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLSL_ZA_ZZW_4x4 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLAL_ZA_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLAL_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_UMLAL_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_UMLAL_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLAL_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLAL_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLSL_ZA_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLSL_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_UMLSL_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_UMLSL_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_UMLSL_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_UMLSL_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLAL_ZA_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLAL_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_SMLAL_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_SMLAL_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLAL_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLAL_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_SMLSL_ZA_ZZV_4x1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLSL_ZA_ZZV_4x1 128 esize m n nreg offset v)
  | 256 => (execute_SMLSL_ZA_ZZV_4x1 256 esize m n nreg offset v)
  | 512 => (execute_SMLSL_ZA_ZZV_4x1 512 esize m n nreg offset v)
  | 1024 => (execute_SMLSL_ZA_ZZV_4x1 1024 esize m n nreg offset v)
  | 2048 => (execute_SMLSL_ZA_ZZV_4x1 2048 esize m n nreg offset v)
  | _ => (pure ())

def decode_UMLAL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 1
  match VL with
  | 128 => (execute_UMLAL_ZA_ZZi_1 128 esize index m n nreg offset v)
  | 256 => (execute_UMLAL_ZA_ZZi_1 256 esize index m n nreg offset v)
  | 512 => (execute_UMLAL_ZA_ZZi_1 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLAL_ZA_ZZi_1 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLAL_ZA_ZZi_1 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLSL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 1
  match VL with
  | 128 => (execute_UMLSL_ZA_ZZi_1 128 esize index m n nreg offset v)
  | 256 => (execute_UMLSL_ZA_ZZi_1 256 esize index m n nreg offset v)
  | 512 => (execute_UMLSL_ZA_ZZi_1 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLSL_ZA_ZZi_1 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLSL_ZA_ZZi_1 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLAL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 1
  match VL with
  | 128 => (execute_SMLAL_ZA_ZZi_1 128 esize index m n nreg offset v)
  | 256 => (execute_SMLAL_ZA_ZZi_1 256 esize index m n nreg offset v)
  | 512 => (execute_SMLAL_ZA_ZZi_1 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLAL_ZA_ZZi_1 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLAL_ZA_ZZi_1 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLSL_ZA_ZZi_1 (Zm : (BitVec 4)) (i3h : (BitVec 1)) (Rv : (BitVec 2)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (U : (BitVec 1)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 1
  match VL with
  | 128 => (execute_SMLSL_ZA_ZZi_1 128 esize index m n nreg offset v)
  | 256 => (execute_SMLSL_ZA_ZZi_1 256 esize index m n nreg offset v)
  | 512 => (execute_SMLSL_ZA_ZZi_1 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLSL_ZA_ZZi_1 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLSL_ZA_ZZi_1 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLAL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLAL_ZA_ZZi_2xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLAL_ZA_ZZi_2xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLAL_ZA_ZZi_2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLAL_ZA_ZZi_2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLAL_ZA_ZZi_2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLSL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 2
  match VL with
  | 128 => (execute_UMLSL_ZA_ZZi_2xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLSL_ZA_ZZi_2xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLSL_ZA_ZZi_2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLSL_ZA_ZZi_2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLSL_ZA_ZZi_2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLAL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLAL_ZA_ZZi_2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLAL_ZA_ZZi_2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLAL_ZA_ZZi_2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLAL_ZA_ZZi_2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLAL_ZA_ZZi_2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLSL_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 2
  match VL with
  | 128 => (execute_SMLSL_ZA_ZZi_2xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLSL_ZA_ZZi_2xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLSL_ZA_ZZi_2xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLSL_ZA_ZZi_2xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLSL_ZA_ZZi_2xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLAL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLAL_ZA_ZZi_4xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLAL_ZA_ZZi_4xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLAL_ZA_ZZi_4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLAL_ZA_ZZi_4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLAL_ZA_ZZi_4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMLSL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 4
  match VL with
  | 128 => (execute_UMLSL_ZA_ZZi_4xi 128 esize index m n nreg offset v)
  | 256 => (execute_UMLSL_ZA_ZZi_4xi 256 esize index m n nreg offset v)
  | 512 => (execute_UMLSL_ZA_ZZi_4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_UMLSL_ZA_ZZi_4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_UMLSL_ZA_ZZi_4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLAL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLAL_ZA_ZZi_4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLAL_ZA_ZZi_4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLAL_ZA_ZZi_4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLAL_ZA_ZZi_4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLAL_ZA_ZZi_4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_SMLSL_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (U : (BitVec 1)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let index := (BitVec.toNat (i3h +++ i3l))
  let nreg := 4
  match VL with
  | 128 => (execute_SMLSL_ZA_ZZi_4xi 128 esize index m n nreg offset v)
  | 256 => (execute_SMLSL_ZA_ZZi_4xi 256 esize index m n nreg offset v)
  | 512 => (execute_SMLSL_ZA_ZZi_4xi 512 esize index m n nreg offset v)
  | 1024 => (execute_SMLSL_ZA_ZZi_4xi 1024 esize index m n nreg offset v)
  | 2048 => (execute_SMLSL_ZA_ZZi_4xi 2048 esize index m n nreg offset v)
  | _ => (pure ())

def decode_UMAX_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMAX_MZ_ZZW_2x2 128 dn esize m nreg is_unsigned)
  | 256 => (execute_UMAX_MZ_ZZW_2x2 256 dn esize m nreg is_unsigned)
  | 512 => (execute_UMAX_MZ_ZZW_2x2 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_UMAX_MZ_ZZW_2x2 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_UMAX_MZ_ZZW_2x2 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_SMAX_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMAX_MZ_ZZW_2x2 128 dn esize m nreg is_unsigned)
  | 256 => (execute_SMAX_MZ_ZZW_2x2 256 dn esize m nreg is_unsigned)
  | 512 => (execute_SMAX_MZ_ZZW_2x2 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_SMAX_MZ_ZZW_2x2 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_SMAX_MZ_ZZW_2x2 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_UMAX_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMAX_MZ_ZZV_2x1 128 dn esize m nreg is_unsigned)
  | 256 => (execute_UMAX_MZ_ZZV_2x1 256 dn esize m nreg is_unsigned)
  | 512 => (execute_UMAX_MZ_ZZV_2x1 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_UMAX_MZ_ZZV_2x1 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_UMAX_MZ_ZZV_2x1 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_SMAX_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMAX_MZ_ZZV_2x1 128 dn esize m nreg is_unsigned)
  | 256 => (execute_SMAX_MZ_ZZV_2x1 256 dn esize m nreg is_unsigned)
  | 512 => (execute_SMAX_MZ_ZZV_2x1 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_SMAX_MZ_ZZV_2x1 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_SMAX_MZ_ZZV_2x1 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_UMAX_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMAX_MZ_ZZW_4x4 128 dn esize m nreg is_unsigned)
  | 256 => (execute_UMAX_MZ_ZZW_4x4 256 dn esize m nreg is_unsigned)
  | 512 => (execute_UMAX_MZ_ZZW_4x4 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_UMAX_MZ_ZZW_4x4 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_UMAX_MZ_ZZW_4x4 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_SMAX_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMAX_MZ_ZZW_4x4 128 dn esize m nreg is_unsigned)
  | 256 => (execute_SMAX_MZ_ZZW_4x4 256 dn esize m nreg is_unsigned)
  | 512 => (execute_SMAX_MZ_ZZW_4x4 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_SMAX_MZ_ZZW_4x4 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_SMAX_MZ_ZZW_4x4 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_UMAX_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMAX_MZ_ZZV_4x1 128 dn esize m nreg is_unsigned)
  | 256 => (execute_UMAX_MZ_ZZV_4x1 256 dn esize m nreg is_unsigned)
  | 512 => (execute_UMAX_MZ_ZZV_4x1 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_UMAX_MZ_ZZV_4x1 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_UMAX_MZ_ZZV_4x1 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_SMAX_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMAX_MZ_ZZV_4x1 128 dn esize m nreg is_unsigned)
  | 256 => (execute_SMAX_MZ_ZZV_4x1 256 dn esize m nreg is_unsigned)
  | 512 => (execute_SMAX_MZ_ZZV_4x1 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_SMAX_MZ_ZZV_4x1 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_SMAX_MZ_ZZV_4x1 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_UMIN_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMIN_MZ_ZZW_2x2 128 dn esize m nreg is_unsigned)
  | 256 => (execute_UMIN_MZ_ZZW_2x2 256 dn esize m nreg is_unsigned)
  | 512 => (execute_UMIN_MZ_ZZW_2x2 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_UMIN_MZ_ZZW_2x2 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_UMIN_MZ_ZZW_2x2 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_SMIN_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMIN_MZ_ZZW_2x2 128 dn esize m nreg is_unsigned)
  | 256 => (execute_SMIN_MZ_ZZW_2x2 256 dn esize m nreg is_unsigned)
  | 512 => (execute_SMIN_MZ_ZZW_2x2 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_SMIN_MZ_ZZW_2x2 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_SMIN_MZ_ZZW_2x2 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_UMIN_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMIN_MZ_ZZV_2x1 128 dn esize m nreg is_unsigned)
  | 256 => (execute_UMIN_MZ_ZZV_2x1 256 dn esize m nreg is_unsigned)
  | 512 => (execute_UMIN_MZ_ZZV_2x1 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_UMIN_MZ_ZZV_2x1 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_UMIN_MZ_ZZV_2x1 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_SMIN_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMIN_MZ_ZZV_2x1 128 dn esize m nreg is_unsigned)
  | 256 => (execute_SMIN_MZ_ZZV_2x1 256 dn esize m nreg is_unsigned)
  | 512 => (execute_SMIN_MZ_ZZV_2x1 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_SMIN_MZ_ZZV_2x1 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_SMIN_MZ_ZZV_2x1 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_UMIN_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMIN_MZ_ZZW_4x4 128 dn esize m nreg is_unsigned)
  | 256 => (execute_UMIN_MZ_ZZW_4x4 256 dn esize m nreg is_unsigned)
  | 512 => (execute_UMIN_MZ_ZZW_4x4 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_UMIN_MZ_ZZW_4x4 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_UMIN_MZ_ZZW_4x4 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_SMIN_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMIN_MZ_ZZW_4x4 128 dn esize m nreg is_unsigned)
  | 256 => (execute_SMIN_MZ_ZZW_4x4 256 dn esize m nreg is_unsigned)
  | 512 => (execute_SMIN_MZ_ZZW_4x4 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_SMIN_MZ_ZZW_4x4 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_SMIN_MZ_ZZW_4x4 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_UMIN_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMIN_MZ_ZZV_4x1 128 dn esize m nreg is_unsigned)
  | 256 => (execute_UMIN_MZ_ZZV_4x1 256 dn esize m nreg is_unsigned)
  | 512 => (execute_UMIN_MZ_ZZV_4x1 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_UMIN_MZ_ZZV_4x1 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_UMIN_MZ_ZZV_4x1 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_SMIN_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMIN_MZ_ZZV_4x1 128 dn esize m nreg is_unsigned)
  | 256 => (execute_SMIN_MZ_ZZV_4x1 256 dn esize m nreg is_unsigned)
  | 512 => (execute_SMIN_MZ_ZZV_4x1 512 dn esize m nreg is_unsigned)
  | 1024 => (execute_SMIN_MZ_ZZV_4x1 1024 dn esize m nreg is_unsigned)
  | 2048 => (execute_SMIN_MZ_ZZV_4x1 2048 dn esize m nreg is_unsigned)
  | _ => (pure ())

def decode_URSHL_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_URSHL_MZ_ZZW_2x2 128 dn esize m nreg)
  | 256 => (execute_URSHL_MZ_ZZW_2x2 256 dn esize m nreg)
  | 512 => (execute_URSHL_MZ_ZZW_2x2 512 dn esize m nreg)
  | 1024 => (execute_URSHL_MZ_ZZW_2x2 1024 dn esize m nreg)
  | 2048 => (execute_URSHL_MZ_ZZW_2x2 2048 dn esize m nreg)
  | _ => (pure ())

def decode_SRSHL_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_SRSHL_MZ_ZZW_2x2 128 dn esize m nreg)
  | 256 => (execute_SRSHL_MZ_ZZW_2x2 256 dn esize m nreg)
  | 512 => (execute_SRSHL_MZ_ZZW_2x2 512 dn esize m nreg)
  | 1024 => (execute_SRSHL_MZ_ZZW_2x2 1024 dn esize m nreg)
  | 2048 => (execute_SRSHL_MZ_ZZW_2x2 2048 dn esize m nreg)
  | _ => (pure ())

def decode_URSHL_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_URSHL_MZ_ZZV_2x1 128 dn esize m nreg)
  | 256 => (execute_URSHL_MZ_ZZV_2x1 256 dn esize m nreg)
  | 512 => (execute_URSHL_MZ_ZZV_2x1 512 dn esize m nreg)
  | 1024 => (execute_URSHL_MZ_ZZV_2x1 1024 dn esize m nreg)
  | 2048 => (execute_URSHL_MZ_ZZV_2x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_SRSHL_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_SRSHL_MZ_ZZV_2x1 128 dn esize m nreg)
  | 256 => (execute_SRSHL_MZ_ZZV_2x1 256 dn esize m nreg)
  | 512 => (execute_SRSHL_MZ_ZZV_2x1 512 dn esize m nreg)
  | 1024 => (execute_SRSHL_MZ_ZZV_2x1 1024 dn esize m nreg)
  | 2048 => (execute_SRSHL_MZ_ZZV_2x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_URSHL_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_URSHL_MZ_ZZW_4x4 128 dn esize m nreg)
  | 256 => (execute_URSHL_MZ_ZZW_4x4 256 dn esize m nreg)
  | 512 => (execute_URSHL_MZ_ZZW_4x4 512 dn esize m nreg)
  | 1024 => (execute_URSHL_MZ_ZZW_4x4 1024 dn esize m nreg)
  | 2048 => (execute_URSHL_MZ_ZZW_4x4 2048 dn esize m nreg)
  | _ => (pure ())

def decode_SRSHL_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_SRSHL_MZ_ZZW_4x4 128 dn esize m nreg)
  | 256 => (execute_SRSHL_MZ_ZZW_4x4 256 dn esize m nreg)
  | 512 => (execute_SRSHL_MZ_ZZW_4x4 512 dn esize m nreg)
  | 1024 => (execute_SRSHL_MZ_ZZW_4x4 1024 dn esize m nreg)
  | 2048 => (execute_SRSHL_MZ_ZZW_4x4 2048 dn esize m nreg)
  | _ => (pure ())

def decode_URSHL_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_URSHL_MZ_ZZV_4x1 128 dn esize m nreg)
  | 256 => (execute_URSHL_MZ_ZZV_4x1 256 dn esize m nreg)
  | 512 => (execute_URSHL_MZ_ZZV_4x1 512 dn esize m nreg)
  | 1024 => (execute_URSHL_MZ_ZZV_4x1 1024 dn esize m nreg)
  | 2048 => (execute_URSHL_MZ_ZZV_4x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_SRSHL_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_SRSHL_MZ_ZZV_4x1 128 dn esize m nreg)
  | 256 => (execute_SRSHL_MZ_ZZV_4x1 256 dn esize m nreg)
  | 512 => (execute_SRSHL_MZ_ZZV_4x1 512 dn esize m nreg)
  | 1024 => (execute_SRSHL_MZ_ZZV_4x1 1024 dn esize m nreg)
  | 2048 => (execute_SRSHL_MZ_ZZV_4x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_SQDMULH_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_SQDMULH_MZ_ZZW_2x2 128 dn esize m nreg)
  | 256 => (execute_SQDMULH_MZ_ZZW_2x2 256 dn esize m nreg)
  | 512 => (execute_SQDMULH_MZ_ZZW_2x2 512 dn esize m nreg)
  | 1024 => (execute_SQDMULH_MZ_ZZW_2x2 1024 dn esize m nreg)
  | 2048 => (execute_SQDMULH_MZ_ZZW_2x2 2048 dn esize m nreg)
  | _ => (pure ())

def decode_SQDMULH_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_SQDMULH_MZ_ZZV_2x1 128 dn esize m nreg)
  | 256 => (execute_SQDMULH_MZ_ZZV_2x1 256 dn esize m nreg)
  | 512 => (execute_SQDMULH_MZ_ZZV_2x1 512 dn esize m nreg)
  | 1024 => (execute_SQDMULH_MZ_ZZV_2x1 1024 dn esize m nreg)
  | 2048 => (execute_SQDMULH_MZ_ZZV_2x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_SQDMULH_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_SQDMULH_MZ_ZZW_4x4 128 dn esize m nreg)
  | 256 => (execute_SQDMULH_MZ_ZZW_4x4 256 dn esize m nreg)
  | 512 => (execute_SQDMULH_MZ_ZZW_4x4 512 dn esize m nreg)
  | 1024 => (execute_SQDMULH_MZ_ZZW_4x4 1024 dn esize m nreg)
  | 2048 => (execute_SQDMULH_MZ_ZZW_4x4 2048 dn esize m nreg)
  | _ => (pure ())

def decode_SQDMULH_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_SQDMULH_MZ_ZZV_4x1 128 dn esize m nreg)
  | 256 => (execute_SQDMULH_MZ_ZZV_4x1 256 dn esize m nreg)
  | 512 => (execute_SQDMULH_MZ_ZZV_4x1 512 dn esize m nreg)
  | 1024 => (execute_SQDMULH_MZ_ZZV_4x1 1024 dn esize m nreg)
  | 2048 => (execute_SQDMULH_MZ_ZZV_4x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_ADD_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_ADD_MZ_ZZV_2x1 128 dn esize m nreg)
  | 256 => (execute_ADD_MZ_ZZV_2x1 256 dn esize m nreg)
  | 512 => (execute_ADD_MZ_ZZV_2x1 512 dn esize m nreg)
  | 1024 => (execute_ADD_MZ_ZZV_2x1 1024 dn esize m nreg)
  | 2048 => (execute_ADD_MZ_ZZV_2x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_ADD_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_ADD_MZ_ZZV_4x1 128 dn esize m nreg)
  | 256 => (execute_ADD_MZ_ZZV_4x1 256 dn esize m nreg)
  | 512 => (execute_ADD_MZ_ZZV_4x1 512 dn esize m nreg)
  | 1024 => (execute_ADD_MZ_ZZV_4x1 1024 dn esize m nreg)
  | 2048 => (execute_ADD_MZ_ZZV_4x1 2048 dn esize m nreg)
  | _ => (pure ())

def decode_UCLAMP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_UCLAMP_MZ_ZZ_2 128 d esize m n nreg)
  | 256 => (execute_UCLAMP_MZ_ZZ_2 256 d esize m n nreg)
  | 512 => (execute_UCLAMP_MZ_ZZ_2 512 d esize m n nreg)
  | 1024 => (execute_UCLAMP_MZ_ZZ_2 1024 d esize m n nreg)
  | 2048 => (execute_UCLAMP_MZ_ZZ_2 2048 d esize m n nreg)
  | _ => (pure ())

def decode_SCLAMP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_SCLAMP_MZ_ZZ_2 128 d esize m n nreg)
  | 256 => (execute_SCLAMP_MZ_ZZ_2 256 d esize m n nreg)
  | 512 => (execute_SCLAMP_MZ_ZZ_2 512 d esize m n nreg)
  | 1024 => (execute_SCLAMP_MZ_ZZ_2 1024 d esize m n nreg)
  | 2048 => (execute_SCLAMP_MZ_ZZ_2 2048 d esize m n nreg)
  | _ => (pure ())

def decode_UCLAMP_MZ_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_UCLAMP_MZ_ZZ_4 128 d esize m n nreg)
  | 256 => (execute_UCLAMP_MZ_ZZ_4 256 d esize m n nreg)
  | 512 => (execute_UCLAMP_MZ_ZZ_4 512 d esize m n nreg)
  | 1024 => (execute_UCLAMP_MZ_ZZ_4 1024 d esize m n nreg)
  | 2048 => (execute_UCLAMP_MZ_ZZ_4 2048 d esize m n nreg)
  | _ => (pure ())

def decode_SCLAMP_MZ_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_SCLAMP_MZ_ZZ_4 128 d esize m n nreg)
  | 256 => (execute_SCLAMP_MZ_ZZ_4 256 d esize m n nreg)
  | 512 => (execute_SCLAMP_MZ_ZZ_4 512 d esize m n nreg)
  | 1024 => (execute_SCLAMP_MZ_ZZ_4 1024 d esize m n nreg)
  | 2048 => (execute_SCLAMP_MZ_ZZ_4 2048 d esize m n nreg)
  | _ => (pure ())

def decode_UUNPK_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UUNPK_MZ_Z_2 128 d esize n nreg is_unsigned)
  | 256 => (execute_UUNPK_MZ_Z_2 256 d esize n nreg is_unsigned)
  | 512 => (execute_UUNPK_MZ_Z_2 512 d esize n nreg is_unsigned)
  | 1024 => (execute_UUNPK_MZ_Z_2 1024 d esize n nreg is_unsigned)
  | 2048 => (execute_UUNPK_MZ_Z_2 2048 d esize n nreg is_unsigned)
  | _ => (pure ())

def decode_SUNPK_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SUNPK_MZ_Z_2 128 d esize n nreg is_unsigned)
  | 256 => (execute_SUNPK_MZ_Z_2 256 d esize n nreg is_unsigned)
  | 512 => (execute_SUNPK_MZ_Z_2 512 d esize n nreg is_unsigned)
  | 1024 => (execute_SUNPK_MZ_Z_2 1024 d esize n nreg is_unsigned)
  | 2048 => (execute_SUNPK_MZ_Z_2 2048 d esize n nreg is_unsigned)
  | _ => (pure ())

def decode_UUNPK_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UUNPK_MZ_Z_4 128 d esize n nreg is_unsigned)
  | 256 => (execute_UUNPK_MZ_Z_4 256 d esize n nreg is_unsigned)
  | 512 => (execute_UUNPK_MZ_Z_4 512 d esize n nreg is_unsigned)
  | 1024 => (execute_UUNPK_MZ_Z_4 1024 d esize n nreg is_unsigned)
  | 2048 => (execute_UUNPK_MZ_Z_4 2048 d esize n nreg is_unsigned)
  | _ => (pure ())

def decode_SUNPK_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SUNPK_MZ_Z_4 128 d esize n nreg is_unsigned)
  | 256 => (execute_SUNPK_MZ_Z_4 256 d esize n nreg is_unsigned)
  | 512 => (execute_SUNPK_MZ_Z_4 512 d esize n nreg is_unsigned)
  | 1024 => (execute_SUNPK_MZ_Z_4 1024 d esize n nreg is_unsigned)
  | 2048 => (execute_SUNPK_MZ_Z_4 2048 d esize n nreg is_unsigned)
  | _ => (pure ())

def decode_SQRSHR_Z_MZ2__ (imm4 : (BitVec 4)) (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  let shift := (esize -i (BitVec.toNat imm4))
  match VL with
  | 128 => (execute_SQRSHR_Z_MZ2__ 128 d esize n shift)
  | 256 => (execute_SQRSHR_Z_MZ2__ 256 d esize n shift)
  | 512 => (execute_SQRSHR_Z_MZ2__ 512 d esize n shift)
  | 1024 => (execute_SQRSHR_Z_MZ2__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHR_Z_MZ2__ 2048 d esize n shift)
  | _ => (pure ())

def decode_UQRSHR_Z_MZ2__ (imm4 : (BitVec 4)) (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  let shift := (esize -i (BitVec.toNat imm4))
  match VL with
  | 128 => (execute_UQRSHR_Z_MZ2__ 128 d esize n shift)
  | 256 => (execute_UQRSHR_Z_MZ2__ 256 d esize n shift)
  | 512 => (execute_UQRSHR_Z_MZ2__ 512 d esize n shift)
  | 1024 => (execute_UQRSHR_Z_MZ2__ 1024 d esize n shift)
  | 2048 => (execute_UQRSHR_Z_MZ2__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQRSHRU_Z_MZ2__ (imm4 : (BitVec 4)) (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  let shift := (esize -i (BitVec.toNat imm4))
  match VL with
  | 128 => (execute_SQRSHRU_Z_MZ2__ 128 d esize n shift)
  | 256 => (execute_SQRSHRU_Z_MZ2__ 256 d esize n shift)
  | 512 => (execute_SQRSHRU_Z_MZ2__ 512 d esize n shift)
  | 1024 => (execute_SQRSHRU_Z_MZ2__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHRU_Z_MZ2__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQRSHRN_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b00#2 : (BitVec 2))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
      then (pure 8)
      else (pure 16)) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  let shift := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 => (execute_SQRSHRN_Z_MZ4__ 128 d esize n shift)
  | 256 => (execute_SQRSHRN_Z_MZ4__ 256 d esize n shift)
  | 512 => (execute_SQRSHRN_Z_MZ4__ 512 d esize n shift)
  | 1024 => (execute_SQRSHRN_Z_MZ4__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHRN_Z_MZ4__ 2048 d esize n shift)
  | _ => (pure ())

def decode_UQRSHRN_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b00#2 : (BitVec 2))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
      then (pure 8)
      else (pure 16)) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  let shift := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 => (execute_UQRSHRN_Z_MZ4__ 128 d esize n shift)
  | 256 => (execute_UQRSHRN_Z_MZ4__ 256 d esize n shift)
  | 512 => (execute_UQRSHRN_Z_MZ4__ 512 d esize n shift)
  | 1024 => (execute_UQRSHRN_Z_MZ4__ 1024 d esize n shift)
  | 2048 => (execute_UQRSHRN_Z_MZ4__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQRSHRUN_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b00#2 : (BitVec 2))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
      then (pure 8)
      else (pure 16)) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  let shift := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 => (execute_SQRSHRUN_Z_MZ4__ 128 d esize n shift)
  | 256 => (execute_SQRSHRUN_Z_MZ4__ 256 d esize n shift)
  | 512 => (execute_SQRSHRUN_Z_MZ4__ 512 d esize n shift)
  | 1024 => (execute_SQRSHRUN_Z_MZ4__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHRUN_Z_MZ4__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQRSHR_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b00#2 : (BitVec 2))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
      then (pure 8)
      else (pure 16)) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  let shift := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 => (execute_SQRSHR_Z_MZ4__ 128 d esize n shift)
  | 256 => (execute_SQRSHR_Z_MZ4__ 256 d esize n shift)
  | 512 => (execute_SQRSHR_Z_MZ4__ 512 d esize n shift)
  | 1024 => (execute_SQRSHR_Z_MZ4__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHR_Z_MZ4__ 2048 d esize n shift)
  | _ => (pure ())

def decode_UQRSHR_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b00#2 : (BitVec 2))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
      then (pure 8)
      else (pure 16)) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  let shift := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 => (execute_UQRSHR_Z_MZ4__ 128 d esize n shift)
  | 256 => (execute_UQRSHR_Z_MZ4__ 256 d esize n shift)
  | 512 => (execute_UQRSHR_Z_MZ4__ 512 d esize n shift)
  | 1024 => (execute_UQRSHR_Z_MZ4__ 1024 d esize n shift)
  | 2048 => (execute_UQRSHR_Z_MZ4__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQRSHRU_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b00#2 : (BitVec 2))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
      then (pure 8)
      else (pure 16)) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  let shift := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
  match VL with
  | 128 => (execute_SQRSHRU_Z_MZ4__ 128 d esize n shift)
  | 256 => (execute_SQRSHRU_Z_MZ4__ 256 d esize n shift)
  | 512 => (execute_SQRSHRU_Z_MZ4__ 512 d esize n shift)
  | 1024 => (execute_SQRSHRU_Z_MZ4__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHRU_Z_MZ4__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQCVT_Z_MZ2__ (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQCVT_Z_MZ2__ 128 d esize n)
  | 256 => (execute_SQCVT_Z_MZ2__ 256 d esize n)
  | 512 => (execute_SQCVT_Z_MZ2__ 512 d esize n)
  | 1024 => (execute_SQCVT_Z_MZ2__ 1024 d esize n)
  | 2048 => (execute_SQCVT_Z_MZ2__ 2048 d esize n)
  | _ => (pure ())

def decode_UQCVT_Z_MZ2__ (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_UQCVT_Z_MZ2__ 128 d esize n)
  | 256 => (execute_UQCVT_Z_MZ2__ 256 d esize n)
  | 512 => (execute_UQCVT_Z_MZ2__ 512 d esize n)
  | 1024 => (execute_UQCVT_Z_MZ2__ 1024 d esize n)
  | 2048 => (execute_UQCVT_Z_MZ2__ 2048 d esize n)
  | _ => (pure ())

def decode_SQCVTU_Z_MZ2__ (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQCVTU_Z_MZ2__ 128 d esize n)
  | 256 => (execute_SQCVTU_Z_MZ2__ 256 d esize n)
  | 512 => (execute_SQCVTU_Z_MZ2__ 512 d esize n)
  | 1024 => (execute_SQCVTU_Z_MZ2__ 1024 d esize n)
  | 2048 => (execute_SQCVTU_Z_MZ2__ 2048 d esize n)
  | _ => (pure ())

def decode_SQCVTN_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "src/instrs64_sme.sail:34431.103-34431.104"
      (execute_SQCVTN_Z_MZ4__ 128 d esize n))
  | 256 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "src/instrs64_sme.sail:34435.103-34435.104"
      (execute_SQCVTN_Z_MZ4__ 256 d esize n))
  | 512 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "src/instrs64_sme.sail:34439.103-34439.104"
      (execute_SQCVTN_Z_MZ4__ 512 d esize n))
  | 1024 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "src/instrs64_sme.sail:34443.104-34443.105"
      (execute_SQCVTN_Z_MZ4__ 1024 d esize n))
  | 2048 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "src/instrs64_sme.sail:34447.104-34447.105"
      (execute_SQCVTN_Z_MZ4__ 2048 d esize n))
  | _ => (pure ())

def decode_UQCVTN_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "src/instrs64_sme.sail:34495.103-34495.104"
      (execute_UQCVTN_Z_MZ4__ 128 d esize n))
  | 256 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "src/instrs64_sme.sail:34499.103-34499.104"
      (execute_UQCVTN_Z_MZ4__ 256 d esize n))
  | 512 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "src/instrs64_sme.sail:34503.103-34503.104"
      (execute_UQCVTN_Z_MZ4__ 512 d esize n))
  | 1024 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "src/instrs64_sme.sail:34507.104-34507.105"
      (execute_UQCVTN_Z_MZ4__ 1024 d esize n))
  | 2048 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "src/instrs64_sme.sail:34511.104-34511.105"
      (execute_UQCVTN_Z_MZ4__ 2048 d esize n))
  | _ => (pure ())

def decode_SQCVTUN_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "src/instrs64_sme.sail:34559.103-34559.104"
      (execute_SQCVTUN_Z_MZ4__ 128 d esize n))
  | 256 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "src/instrs64_sme.sail:34563.103-34563.104"
      (execute_SQCVTUN_Z_MZ4__ 256 d esize n))
  | 512 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "src/instrs64_sme.sail:34567.103-34567.104"
      (execute_SQCVTUN_Z_MZ4__ 512 d esize n))
  | 1024 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "src/instrs64_sme.sail:34571.104-34571.105"
      (execute_SQCVTUN_Z_MZ4__ 1024 d esize n))
  | 2048 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "src/instrs64_sme.sail:34575.104-34575.105"
      (execute_SQCVTUN_Z_MZ4__ 2048 d esize n))
  | _ => (pure ())

def decode_SQCVT_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "src/instrs64_sme.sail:34623.103-34623.104"
      (execute_SQCVT_Z_MZ4__ 128 d esize n))
  | 256 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "src/instrs64_sme.sail:34627.103-34627.104"
      (execute_SQCVT_Z_MZ4__ 256 d esize n))
  | 512 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "src/instrs64_sme.sail:34631.103-34631.104"
      (execute_SQCVT_Z_MZ4__ 512 d esize n))
  | 1024 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "src/instrs64_sme.sail:34635.104-34635.105"
      (execute_SQCVT_Z_MZ4__ 1024 d esize n))
  | 2048 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "src/instrs64_sme.sail:34639.104-34639.105"
      (execute_SQCVT_Z_MZ4__ 2048 d esize n))
  | _ => (pure ())

def decode_UQCVT_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "src/instrs64_sme.sail:34687.103-34687.104"
      (execute_UQCVT_Z_MZ4__ 128 d esize n))
  | 256 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "src/instrs64_sme.sail:34691.103-34691.104"
      (execute_UQCVT_Z_MZ4__ 256 d esize n))
  | 512 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "src/instrs64_sme.sail:34695.103-34695.104"
      (execute_UQCVT_Z_MZ4__ 512 d esize n))
  | 1024 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "src/instrs64_sme.sail:34699.104-34699.105"
      (execute_UQCVT_Z_MZ4__ 1024 d esize n))
  | 2048 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "src/instrs64_sme.sail:34703.104-34703.105"
      (execute_UQCVT_Z_MZ4__ 2048 d esize n))
  | _ => (pure ())

def decode_SQCVTU_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat sz))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "src/instrs64_sme.sail:34751.103-34751.104"
      (execute_SQCVTU_Z_MZ4__ 128 d esize n))
  | 256 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "src/instrs64_sme.sail:34755.103-34755.104"
      (execute_SQCVTU_Z_MZ4__ 256 d esize n))
  | 512 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "src/instrs64_sme.sail:34759.103-34759.104"
      (execute_SQCVTU_Z_MZ4__ 512 d esize n))
  | 1024 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "src/instrs64_sme.sail:34763.104-34763.105"
      (execute_SQCVTU_Z_MZ4__ 1024 d esize n))
  | 2048 =>
    (do
      sail_assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "src/instrs64_sme.sail:34767.104-34767.105"
      (execute_SQCVTU_Z_MZ4__ 2048 d esize n))
  | _ => (pure ())

def decode_ZIP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 => (execute_ZIP_MZ_ZZ_2 128 d esize m n)
  | 256 => (execute_ZIP_MZ_ZZ_2 256 d esize m n)
  | 512 => (execute_ZIP_MZ_ZZ_2 512 d esize m n)
  | 1024 => (execute_ZIP_MZ_ZZ_2 1024 d esize m n)
  | 2048 => (execute_ZIP_MZ_ZZ_2 2048 d esize m n)
  | _ => (pure ())

def decode_UZP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 => (execute_UZP_MZ_ZZ_2 128 d esize m n)
  | 256 => (execute_UZP_MZ_ZZ_2 256 d esize m n)
  | 512 => (execute_UZP_MZ_ZZ_2 512 d esize m n)
  | 1024 => (execute_UZP_MZ_ZZ_2 1024 d esize m n)
  | 2048 => (execute_UZP_MZ_ZZ_2 2048 d esize m n)
  | _ => (pure ())

def decode_ZIP_MZ_ZZ_2Q (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 => (execute_ZIP_MZ_ZZ_2Q 128 d esize m n)
  | 256 => (execute_ZIP_MZ_ZZ_2Q 256 d esize m n)
  | 512 => (execute_ZIP_MZ_ZZ_2Q 512 d esize m n)
  | 1024 => (execute_ZIP_MZ_ZZ_2Q 1024 d esize m n)
  | 2048 => (execute_ZIP_MZ_ZZ_2Q 2048 d esize m n)
  | _ => (pure ())

def decode_UZP_MZ_ZZ_2Q (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 => (execute_UZP_MZ_ZZ_2Q 128 d esize m n)
  | 256 => (execute_UZP_MZ_ZZ_2Q 256 d esize m n)
  | 512 => (execute_UZP_MZ_ZZ_2Q 512 d esize m n)
  | 1024 => (execute_UZP_MZ_ZZ_2Q 1024 d esize m n)
  | 2048 => (execute_UZP_MZ_ZZ_2Q 2048 d esize m n)
  | _ => (pure ())

def decode_ZIP_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  match VL with
  | 128 => (execute_ZIP_MZ_Z_4 128 d esize n)
  | 256 => (execute_ZIP_MZ_Z_4 256 d esize n)
  | 512 => (execute_ZIP_MZ_Z_4 512 d esize n)
  | 1024 => (execute_ZIP_MZ_Z_4 1024 d esize n)
  | 2048 => (execute_ZIP_MZ_Z_4 2048 d esize n)
  | _ => (pure ())

def decode_UZP_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  match VL with
  | 128 => (execute_UZP_MZ_Z_4 128 d esize n)
  | 256 => (execute_UZP_MZ_Z_4 256 d esize n)
  | 512 => (execute_UZP_MZ_Z_4 512 d esize n)
  | 1024 => (execute_UZP_MZ_Z_4 1024 d esize n)
  | 2048 => (execute_UZP_MZ_Z_4 2048 d esize n)
  | _ => (pure ())

def decode_ZIP_MZ_Z_4Q (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  match VL with
  | 128 => (execute_ZIP_MZ_Z_4Q 128 d esize n)
  | 256 => (execute_ZIP_MZ_Z_4Q 256 d esize n)
  | 512 => (execute_ZIP_MZ_Z_4Q 512 d esize n)
  | 1024 => (execute_ZIP_MZ_Z_4Q 1024 d esize n)
  | 2048 => (execute_ZIP_MZ_Z_4Q 2048 d esize n)
  | _ => (pure ())

def decode_UZP_MZ_Z_4Q (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  match VL with
  | 128 => (execute_UZP_MZ_Z_4Q 128 d esize n)
  | 256 => (execute_UZP_MZ_Z_4Q 256 d esize n)
  | 512 => (execute_UZP_MZ_Z_4Q 512 d esize n)
  | 1024 => (execute_UZP_MZ_Z_4Q 1024 d esize n)
  | 2048 => (execute_UZP_MZ_Z_4Q 2048 d esize n)
  | _ => (pure ())

def decode_SEL_MZ_P_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 4)) (PNg : (BitVec 3)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let d := (BitVec.toNat (Zd +++ 0#1))
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  match VL with
  | 128 => (execute_SEL_MZ_P_ZZ_2 128 d esize g m n nreg)
  | 256 => (execute_SEL_MZ_P_ZZ_2 256 d esize g m n nreg)
  | 512 => (execute_SEL_MZ_P_ZZ_2 512 d esize g m n nreg)
  | 1024 => (execute_SEL_MZ_P_ZZ_2 1024 d esize g m n nreg)
  | 2048 => (execute_SEL_MZ_P_ZZ_2 2048 d esize g m n nreg)
  | _ => (pure ())

def decode_SEL_MZ_P_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 3)) (PNg : (BitVec 3)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  match VL with
  | 128 => (execute_SEL_MZ_P_ZZ_4 128 d esize g m n nreg)
  | 256 => (execute_SEL_MZ_P_ZZ_4 256 d esize g m n nreg)
  | 512 => (execute_SEL_MZ_P_ZZ_4 512 d esize g m n nreg)
  | 1024 => (execute_SEL_MZ_P_ZZ_4 1024 d esize g m n nreg)
  | 2048 => (execute_SEL_MZ_P_ZZ_4 2048 d esize g m n nreg)
  | _ => (pure ())

def decode_BMOPA_ZA_PP_ZZ_32 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 => (execute_BMOPA_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op)
  | 256 => (execute_BMOPA_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op)
  | 512 => (execute_BMOPA_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op)
  | 1024 => (execute_BMOPA_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op)
  | 2048 => (execute_BMOPA_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op)
  | _ => (pure ())

def decode_BMOPS_ZA_PP_ZZ_32 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 => (execute_BMOPS_ZA_PP_ZZ_32 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op)
  | 256 => (execute_BMOPS_ZA_PP_ZZ_32 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op)
  | 512 => (execute_BMOPS_ZA_PP_ZZ_32 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op)
  | 1024 => (execute_BMOPS_ZA_PP_ZZ_32 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op)
  | 2048 => (execute_BMOPS_ZA_PP_ZZ_32 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op)
  | _ => (pure ())

def decode_SMOPA_ZA32_PP_ZZ_16 (u0 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMOPA_ZA32_PP_ZZ_16 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 256 => (execute_SMOPA_ZA32_PP_ZZ_16 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 512 => (execute_SMOPA_ZA32_PP_ZZ_16 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 1024 => (execute_SMOPA_ZA32_PP_ZZ_16 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 2048 => (execute_SMOPA_ZA32_PP_ZZ_16 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | _ => (pure ())

def decode_UMOPA_ZA32_PP_ZZ_16 (u0 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMOPA_ZA32_PP_ZZ_16 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 256 => (execute_UMOPA_ZA32_PP_ZZ_16 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 512 => (execute_UMOPA_ZA32_PP_ZZ_16 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 1024 => (execute_UMOPA_ZA32_PP_ZZ_16 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 2048 => (execute_UMOPA_ZA32_PP_ZZ_16 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | _ => (pure ())

def decode_SMOPS_ZA32_PP_ZZ_16 (u0 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMOPS_ZA32_PP_ZZ_16 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 256 => (execute_SMOPS_ZA32_PP_ZZ_16 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 512 => (execute_SMOPS_ZA32_PP_ZZ_16 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 1024 => (execute_SMOPS_ZA32_PP_ZZ_16 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 2048 => (execute_SMOPS_ZA32_PP_ZZ_16 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | _ => (pure ())

def decode_UMOPS_ZA32_PP_ZZ_16 (u0 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMOPS_ZA32_PP_ZZ_16 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 256 => (execute_UMOPS_ZA32_PP_ZZ_16 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 512 => (execute_UMOPS_ZA32_PP_ZZ_16 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 1024 => (execute_UMOPS_ZA32_PP_ZZ_16 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | 2048 => (execute_UMOPS_ZA32_PP_ZZ_16 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op is_unsigned)
  | _ => (pure ())

def decode_LUTI2_Z_ZTZ__ (i4 : (BitVec 4)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let isize := 2
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let imm := (BitVec.toNat i4)
  let nreg := 1
  match VL with
  | 128 => (execute_LUTI2_Z_ZTZ__ 128 d esize imm isize n nreg)
  | 256 => (execute_LUTI2_Z_ZTZ__ 256 d esize imm isize n nreg)
  | 512 => (execute_LUTI2_Z_ZTZ__ 512 d esize imm isize n nreg)
  | 1024 => (execute_LUTI2_Z_ZTZ__ 1024 d esize imm isize n nreg)
  | 2048 => (execute_LUTI2_Z_ZTZ__ 2048 d esize imm isize n nreg)
  | _ => (pure ())

def decode_LUTI4_Z_ZTZ__ (i3 : (BitVec 3)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let isize := 4
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let imm := (BitVec.toNat i3)
  let nreg := 1
  match VL with
  | 128 => (execute_LUTI4_Z_ZTZ__ 128 d esize imm isize n nreg)
  | 256 => (execute_LUTI4_Z_ZTZ__ 256 d esize imm isize n nreg)
  | 512 => (execute_LUTI4_Z_ZTZ__ 512 d esize imm isize n nreg)
  | 1024 => (execute_LUTI4_Z_ZTZ__ 1024 d esize imm isize n nreg)
  | 2048 => (execute_LUTI4_Z_ZTZ__ 2048 d esize imm isize n nreg)
  | _ => (pure ())

def decode_LUTI2_MZ2_ZTZ_1 (i3 : (BitVec 3)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let isize := 2
  let n := (BitVec.toNat Zn)
  let dstride := 1
  let d := (BitVec.toNat (Zd +++ 0#1))
  let imm := (BitVec.toNat i3)
  let nreg := 2
  match VL with
  | 128 => (execute_LUTI2_MZ2_ZTZ_1 128 d dstride esize imm isize n nreg)
  | 256 => (execute_LUTI2_MZ2_ZTZ_1 256 d dstride esize imm isize n nreg)
  | 512 => (execute_LUTI2_MZ2_ZTZ_1 512 d dstride esize imm isize n nreg)
  | 1024 => (execute_LUTI2_MZ2_ZTZ_1 1024 d dstride esize imm isize n nreg)
  | 2048 => (execute_LUTI2_MZ2_ZTZ_1 2048 d dstride esize imm isize n nreg)
  | _ => (pure ())

def decode_LUTI4_MZ2_ZTZ_1 (i2 : (BitVec 2)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let isize := 4
  let n := (BitVec.toNat Zn)
  let dstride := 1
  let d := (BitVec.toNat (Zd +++ 0#1))
  let imm := (BitVec.toNat i2)
  let nreg := 2
  match VL with
  | 128 => (execute_LUTI4_MZ2_ZTZ_1 128 d dstride esize imm isize n nreg)
  | 256 => (execute_LUTI4_MZ2_ZTZ_1 256 d dstride esize imm isize n nreg)
  | 512 => (execute_LUTI4_MZ2_ZTZ_1 512 d dstride esize imm isize n nreg)
  | 1024 => (execute_LUTI4_MZ2_ZTZ_1 1024 d dstride esize imm isize n nreg)
  | 2048 => (execute_LUTI4_MZ2_ZTZ_1 2048 d dstride esize imm isize n nreg)
  | _ => (pure ())

def decode_LUTI2_MZ4_ZTZ_1 (i2 : (BitVec 2)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let isize := 2
  let n := (BitVec.toNat Zn)
  let dstride := 1
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let imm := (BitVec.toNat i2)
  let nreg := 4
  match VL with
  | 128 => (execute_LUTI2_MZ4_ZTZ_1 128 d dstride esize imm isize n nreg)
  | 256 => (execute_LUTI2_MZ4_ZTZ_1 256 d dstride esize imm isize n nreg)
  | 512 => (execute_LUTI2_MZ4_ZTZ_1 512 d dstride esize imm isize n nreg)
  | 1024 => (execute_LUTI2_MZ4_ZTZ_1 1024 d dstride esize imm isize n nreg)
  | 2048 => (execute_LUTI2_MZ4_ZTZ_1 2048 d dstride esize imm isize n nreg)
  | _ => (pure ())

def decode_LUTI4_MZ4_ZTZ_1 (i1 : (BitVec 1)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let isize := 4
  let n := (BitVec.toNat Zn)
  let dstride := 1
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let imm := (BitVec.toNat i1)
  let nreg := 4
  match VL with
  | 128 => (execute_LUTI4_MZ4_ZTZ_1 128 d dstride esize imm isize n nreg)
  | 256 => (execute_LUTI4_MZ4_ZTZ_1 256 d dstride esize imm isize n nreg)
  | 512 => (execute_LUTI4_MZ4_ZTZ_1 512 d dstride esize imm isize n nreg)
  | 1024 => (execute_LUTI4_MZ4_ZTZ_1 1024 d dstride esize imm isize n nreg)
  | 2048 => (execute_LUTI4_MZ4_ZTZ_1 2048 d dstride esize imm isize n nreg)
  | _ => (pure ())

def decode_LDR_ZT_BR__ (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  (execute_LDR_ZT_BR__ n)

def decode_STR_ZT_BR__ (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  (execute_STR_ZT_BR__ n)

def decode_ZERO_ZT_I__ (_ : Unit) : SailM Unit := do
  if ((! (← (HaveSME2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_ZERO_ZT_I__ ())

def decode_MOVT_R_ZT__ (off3 : (BitVec 3)) (Rt : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSME2 ())))) <||> (do
       (pure (! (← (Halted ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let offset := (BitVec.toNat off3)
  (execute_MOVT_R_ZT__ offset t)

def decode_MOVT_ZT_R__ (off3 : (BitVec 3)) (Rt : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSME2 ())))) <||> (do
       (pure (! (← (Halted ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let offset := (BitVec.toNat off3)
  (execute_MOVT_ZT_R__ offset t)

def decode_RDSVL_R_I__ (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
  let SVL ← do (CurrentSVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let imm := (BitVec.toInt imm6)
  match SVL with
  | 128 => (execute_RDSVL_R_I__ 128 d imm)
  | 256 => (execute_RDSVL_R_I__ 256 d imm)
  | 512 => (execute_RDSVL_R_I__ 512 d imm)
  | 1024 => (execute_RDSVL_R_I__ 1024 d imm)
  | 2048 => (execute_RDSVL_R_I__ 2048 d imm)
  | _ => (pure ())

def decode_ADDSPL_R_RI__ (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
  let SVL ← do (CurrentSVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  let imm := (BitVec.toInt imm6)
  match SVL with
  | 128 => (execute_ADDSPL_R_RI__ 128 d imm n)
  | 256 => (execute_ADDSPL_R_RI__ 256 d imm n)
  | 512 => (execute_ADDSPL_R_RI__ 512 d imm n)
  | 1024 => (execute_ADDSPL_R_RI__ 1024 d imm n)
  | 2048 => (execute_ADDSPL_R_RI__ 2048 d imm n)
  | _ => (pure ())

def decode_ADDSVL_R_RI__ (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
  let SVL ← do (CurrentSVL_read ())
  if ((! (← (HaveSME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  let imm := (BitVec.toInt imm6)
  match SVL with
  | 128 => (execute_ADDSVL_R_RI__ 128 d imm n)
  | 256 => (execute_ADDSVL_R_RI__ 256 d imm n)
  | 512 => (execute_ADDSVL_R_RI__ 512 d imm n)
  | 1024 => (execute_ADDSVL_R_RI__ 1024 d imm n)
  | 2048 => (execute_ADDSVL_R_RI__ 2048 d imm n)
  | _ => (pure ())

def decode_ZERO_ZA1_RI_2 (Rv : (BitVec 2)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat off3)
  let ngrp := 2
  match VL with
  | 128 => (execute_ZERO_ZA1_RI_2 128 ngrp offset v)
  | 256 => (execute_ZERO_ZA1_RI_2 256 ngrp offset v)
  | 512 => (execute_ZERO_ZA1_RI_2 512 ngrp offset v)
  | 1024 => (execute_ZERO_ZA1_RI_2 1024 ngrp offset v)
  | 2048 => (execute_ZERO_ZA1_RI_2 2048 ngrp offset v)
  | _ => (pure ())

def decode_ZERO_ZA1_RI_4 (Rv : (BitVec 2)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat off3)
  let ngrp := 4
  match VL with
  | 128 => (execute_ZERO_ZA1_RI_4 128 ngrp offset v)
  | 256 => (execute_ZERO_ZA1_RI_4 256 ngrp offset v)
  | 512 => (execute_ZERO_ZA1_RI_4 512 ngrp offset v)
  | 1024 => (execute_ZERO_ZA1_RI_4 1024 ngrp offset v)
  | 2048 => (execute_ZERO_ZA1_RI_4 2048 ngrp offset v)
  | _ => (pure ())

def decode_ZERO_ZA2_RI_1 (Rv : (BitVec 2)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let ngrp := 1
  let nvec := 2
  match VL with
  | 128 => (execute_ZERO_ZA2_RI_1 128 ngrp nvec offset v)
  | 256 => (execute_ZERO_ZA2_RI_1 256 ngrp nvec offset v)
  | 512 => (execute_ZERO_ZA2_RI_1 512 ngrp nvec offset v)
  | 1024 => (execute_ZERO_ZA2_RI_1 1024 ngrp nvec offset v)
  | 2048 => (execute_ZERO_ZA2_RI_1 2048 ngrp nvec offset v)
  | _ => (pure ())

def decode_ZERO_ZA2_RI_2 (Rv : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let ngrp := 2
  let nvec := 2
  match VL with
  | 128 => (execute_ZERO_ZA2_RI_2 128 ngrp nvec offset v)
  | 256 => (execute_ZERO_ZA2_RI_2 256 ngrp nvec offset v)
  | 512 => (execute_ZERO_ZA2_RI_2 512 ngrp nvec offset v)
  | 1024 => (execute_ZERO_ZA2_RI_2 1024 ngrp nvec offset v)
  | 2048 => (execute_ZERO_ZA2_RI_2 2048 ngrp nvec offset v)
  | _ => (pure ())

def decode_ZERO_ZA2_RI_4 (Rv : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let ngrp := 4
  let nvec := 2
  match VL with
  | 128 => (execute_ZERO_ZA2_RI_4 128 ngrp nvec offset v)
  | 256 => (execute_ZERO_ZA2_RI_4 256 ngrp nvec offset v)
  | 512 => (execute_ZERO_ZA2_RI_4 512 ngrp nvec offset v)
  | 1024 => (execute_ZERO_ZA2_RI_4 1024 ngrp nvec offset v)
  | 2048 => (execute_ZERO_ZA2_RI_4 2048 ngrp nvec offset v)
  | _ => (pure ())

def decode_ZERO_ZA4_RI_1 (Rv : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let ngrp := 1
  let nvec := 4
  match VL with
  | 128 => (execute_ZERO_ZA4_RI_1 128 ngrp nvec offset v)
  | 256 => (execute_ZERO_ZA4_RI_1 256 ngrp nvec offset v)
  | 512 => (execute_ZERO_ZA4_RI_1 512 ngrp nvec offset v)
  | 1024 => (execute_ZERO_ZA4_RI_1 1024 ngrp nvec offset v)
  | 2048 => (execute_ZERO_ZA4_RI_1 2048 ngrp nvec offset v)
  | _ => (pure ())

def decode_ZERO_ZA4_RI_2 (Rv : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let ngrp := 2
  let nvec := 4
  match VL with
  | 128 => (execute_ZERO_ZA4_RI_2 128 ngrp nvec offset v)
  | 256 => (execute_ZERO_ZA4_RI_2 256 ngrp nvec offset v)
  | 512 => (execute_ZERO_ZA4_RI_2 512 ngrp nvec offset v)
  | 1024 => (execute_ZERO_ZA4_RI_2 1024 ngrp nvec offset v)
  | 2048 => (execute_ZERO_ZA4_RI_2 2048 ngrp nvec offset v)
  | _ => (pure ())

def decode_ZERO_ZA4_RI_4 (Rv : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let ngrp := 4
  let nvec := 4
  match VL with
  | 128 => (execute_ZERO_ZA4_RI_4 128 ngrp nvec offset v)
  | 256 => (execute_ZERO_ZA4_RI_4 256 ngrp nvec offset v)
  | 512 => (execute_ZERO_ZA4_RI_4 512 ngrp nvec offset v)
  | 1024 => (execute_ZERO_ZA4_RI_4 1024 ngrp nvec offset v)
  | 2048 => (execute_ZERO_ZA4_RI_4 2048 ngrp nvec offset v)
  | _ => (pure ())

def decode_LUTI2_MZ2_ZTZ_8 (i3 : (BitVec 3)) (size : (BitVec 2)) (Zn : (BitVec 5)) (D : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size == 0b10#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let isize := 2
  let n := (BitVec.toNat Zn)
  let dstride := 8
  let d := (BitVec.toNat ((D +++ 0#1) +++ Zd))
  let imm := (BitVec.toNat i3)
  let nreg := 2
  match VL with
  | 128 => (execute_LUTI2_MZ2_ZTZ_8 128 d dstride esize imm isize n nreg)
  | 256 => (execute_LUTI2_MZ2_ZTZ_8 256 d dstride esize imm isize n nreg)
  | 512 => (execute_LUTI2_MZ2_ZTZ_8 512 d dstride esize imm isize n nreg)
  | 1024 => (execute_LUTI2_MZ2_ZTZ_8 1024 d dstride esize imm isize n nreg)
  | 2048 => (execute_LUTI2_MZ2_ZTZ_8 2048 d dstride esize imm isize n nreg)
  | _ => (pure ())

def decode_LUTI4_MZ2_ZTZ_8 (i2 : (BitVec 2)) (size : (BitVec 2)) (Zn : (BitVec 5)) (D : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size == 0b10#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let isize := 4
  let n := (BitVec.toNat Zn)
  let dstride := 8
  let d := (BitVec.toNat ((D +++ 0#1) +++ Zd))
  let imm := (BitVec.toNat i2)
  let nreg := 2
  match VL with
  | 128 => (execute_LUTI4_MZ2_ZTZ_8 128 d dstride esize imm isize n nreg)
  | 256 => (execute_LUTI4_MZ2_ZTZ_8 256 d dstride esize imm isize n nreg)
  | 512 => (execute_LUTI4_MZ2_ZTZ_8 512 d dstride esize imm isize n nreg)
  | 1024 => (execute_LUTI4_MZ2_ZTZ_8 1024 d dstride esize imm isize n nreg)
  | 2048 => (execute_LUTI4_MZ2_ZTZ_8 2048 d dstride esize imm isize n nreg)
  | _ => (pure ())

def decode_LUTI2_MZ4_ZTZ_4 (i2 : (BitVec 2)) (size : (BitVec 2)) (Zn : (BitVec 5)) (D : (BitVec 1)) (Zd : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size == 0b10#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let isize := 2
  let n := (BitVec.toNat Zn)
  let dstride := 4
  let d := (BitVec.toNat ((D +++ 0b00#2) +++ Zd))
  let imm := (BitVec.toNat i2)
  let nreg := 4
  match VL with
  | 128 => (execute_LUTI2_MZ4_ZTZ_4 128 d dstride esize imm isize n nreg)
  | 256 => (execute_LUTI2_MZ4_ZTZ_4 256 d dstride esize imm isize n nreg)
  | 512 => (execute_LUTI2_MZ4_ZTZ_4 512 d dstride esize imm isize n nreg)
  | 1024 => (execute_LUTI2_MZ4_ZTZ_4 1024 d dstride esize imm isize n nreg)
  | 2048 => (execute_LUTI2_MZ4_ZTZ_4 2048 d dstride esize imm isize n nreg)
  | _ => (pure ())

def decode_LUTI4_MZ4_ZTZ_4 (i1 : (BitVec 1)) (size : (BitVec 2)) (Zn : (BitVec 5)) (D : (BitVec 1)) (Zd : (BitVec 2)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b01#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let isize := 4
  let n := (BitVec.toNat Zn)
  let dstride := 4
  let d := (BitVec.toNat ((D +++ 0b00#2) +++ Zd))
  let imm := (BitVec.toNat i1)
  let nreg := 4
  match VL with
  | 128 => (execute_LUTI4_MZ4_ZTZ_4 128 d dstride esize imm isize n nreg)
  | 256 => (execute_LUTI4_MZ4_ZTZ_4 256 d dstride esize imm isize n nreg)
  | 512 => (execute_LUTI4_MZ4_ZTZ_4 512 d dstride esize imm isize n nreg)
  | 1024 => (execute_LUTI4_MZ4_ZTZ_4 1024 d dstride esize imm isize n nreg)
  | 2048 => (execute_LUTI4_MZ4_ZTZ_4 2048 d dstride esize imm isize n nreg)
  | _ => (pure ())

def decode_MOVAZ_Z_RZA_B (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (off4 : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := 0
  let offset := (BitVec.toNat off4)
  let esize := 8
  let d := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_Z_RZA_B 128 d esize n offset s vertical)
  | 256 => (execute_MOVAZ_Z_RZA_B 256 d esize n offset s vertical)
  | 512 => (execute_MOVAZ_Z_RZA_B 512 d esize n offset s vertical)
  | 1024 => (execute_MOVAZ_Z_RZA_B 1024 d esize n offset s vertical)
  | 2048 => (execute_MOVAZ_Z_RZA_B 2048 d esize n offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_Z_RZA_H (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 1)) (off3 : (BitVec 3)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat off3)
  let esize := 16
  let d := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_Z_RZA_H 128 d esize n offset s vertical)
  | 256 => (execute_MOVAZ_Z_RZA_H 256 d esize n offset s vertical)
  | 512 => (execute_MOVAZ_Z_RZA_H 512 d esize n offset s vertical)
  | 1024 => (execute_MOVAZ_Z_RZA_H 1024 d esize n offset s vertical)
  | 2048 => (execute_MOVAZ_Z_RZA_H 2048 d esize n offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_Z_RZA_W (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 2)) (off2 : (BitVec 2)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat off2)
  let esize := 32
  let d := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_Z_RZA_W 128 d esize n offset s vertical)
  | 256 => (execute_MOVAZ_Z_RZA_W 256 d esize n offset s vertical)
  | 512 => (execute_MOVAZ_Z_RZA_W 512 d esize n offset s vertical)
  | 1024 => (execute_MOVAZ_Z_RZA_W 1024 d esize n offset s vertical)
  | 2048 => (execute_MOVAZ_Z_RZA_W 2048 d esize n offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_Z_RZA_D (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 3)) (o1 : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat o1)
  let esize := 64
  let d := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_Z_RZA_D 128 d esize n offset s vertical)
  | 256 => (execute_MOVAZ_Z_RZA_D 256 d esize n offset s vertical)
  | 512 => (execute_MOVAZ_Z_RZA_D 512 d esize n offset s vertical)
  | 1024 => (execute_MOVAZ_Z_RZA_D 1024 d esize n offset s vertical)
  | 2048 => (execute_MOVAZ_Z_RZA_D 2048 d esize n offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_Z_RZA_Q (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let n := (BitVec.toNat ZAn)
  let offset := 0
  let esize := 128
  let d := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_Z_RZA_Q 128 d esize n offset s vertical)
  | 256 => (execute_MOVAZ_Z_RZA_Q 256 d esize n offset s vertical)
  | 512 => (execute_MOVAZ_Z_RZA_Q 512 d esize n offset s vertical)
  | 1024 => (execute_MOVAZ_Z_RZA_Q 1024 d esize n offset s vertical)
  | 2048 => (execute_MOVAZ_Z_RZA_Q 2048 d esize n offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_MZ2_ZA_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 8
  let d := (BitVec.toNat (Zd +++ 0#1))
  let n := 0
  let offset := (BitVec.toNat (off3 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_MZ2_ZA_B1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVAZ_MZ2_ZA_B1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVAZ_MZ2_ZA_B1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVAZ_MZ2_ZA_B1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVAZ_MZ2_ZA_B1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_MZ2_ZA_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 1)) (off2 : (BitVec 2)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 16
  let d := (BitVec.toNat (Zd +++ 0#1))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat (off2 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_MZ2_ZA_H1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVAZ_MZ2_ZA_H1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVAZ_MZ2_ZA_H1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVAZ_MZ2_ZA_H1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVAZ_MZ2_ZA_H1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_MZ2_ZA_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 2)) (o1 : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 32
  let d := (BitVec.toNat (Zd +++ 0#1))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat (o1 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_MZ2_ZA_W1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVAZ_MZ2_ZA_W1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVAZ_MZ2_ZA_W1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVAZ_MZ2_ZA_W1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVAZ_MZ2_ZA_W1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_MZ2_ZA_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 2
  let esize := 64
  let d := (BitVec.toNat (Zd +++ 0#1))
  let n := (BitVec.toNat ZAn)
  let offset := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_MZ2_ZA_D1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVAZ_MZ2_ZA_D1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVAZ_MZ2_ZA_D1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVAZ_MZ2_ZA_D1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVAZ_MZ2_ZA_D1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_MZ4_ZA_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (off2 : (BitVec 2)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 8
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let n := 0
  let offset := (BitVec.toNat (off2 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_MZ4_ZA_B1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVAZ_MZ4_ZA_B1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVAZ_MZ4_ZA_B1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVAZ_MZ4_ZA_B1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVAZ_MZ4_ZA_B1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_MZ4_ZA_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 1)) (o1 : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 16
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let n := (BitVec.toNat ZAn)
  let offset := (BitVec.toNat (o1 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_MZ4_ZA_H1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVAZ_MZ4_ZA_H1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVAZ_MZ4_ZA_H1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVAZ_MZ4_ZA_H1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVAZ_MZ4_ZA_H1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_MZ4_ZA_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 2)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 32
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let n := (BitVec.toNat ZAn)
  let offset := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_MZ4_ZA_W1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVAZ_MZ4_ZA_W1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVAZ_MZ4_ZA_W1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVAZ_MZ4_ZA_W1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVAZ_MZ4_ZA_W1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_MZ4_ZA_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg := 4
  let esize := 64
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let n := (BitVec.toNat ZAn)
  let offset := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 => (execute_MOVAZ_MZ4_ZA_D1 128 d esize n nreg offset s vertical)
  | 256 => (execute_MOVAZ_MZ4_ZA_D1 256 d esize n nreg offset s vertical)
  | 512 => (execute_MOVAZ_MZ4_ZA_D1 512 d esize n nreg offset s vertical)
  | 1024 => (execute_MOVAZ_MZ4_ZA_D1 1024 d esize n nreg offset s vertical)
  | 2048 => (execute_MOVAZ_MZ4_ZA_D1 2048 d esize n nreg offset s vertical)
  | _ => (pure ())

def decode_MOVAZ_MZ_ZA2_1 (Rv : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat off3)
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_MOVAZ_MZ_ZA2_1 128 d nreg offset v)
  | 256 => (execute_MOVAZ_MZ_ZA2_1 256 d nreg offset v)
  | 512 => (execute_MOVAZ_MZ_ZA2_1 512 d nreg offset v)
  | 1024 => (execute_MOVAZ_MZ_ZA2_1 1024 d nreg offset v)
  | 2048 => (execute_MOVAZ_MZ_ZA2_1 2048 d nreg offset v)
  | _ => (pure ())

def decode_MOVAZ_MZ_ZA4_1 (Rv : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSME2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let offset := (BitVec.toNat off3)
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_MOVAZ_MZ_ZA4_1 128 d nreg offset v)
  | 256 => (execute_MOVAZ_MZ_ZA4_1 256 d nreg offset v)
  | 512 => (execute_MOVAZ_MZ_ZA4_1 512 d nreg offset v)
  | 1024 => (execute_MOVAZ_MZ_ZA4_1 1024 d nreg offset v)
  | 2048 => (execute_MOVAZ_MZ_ZA4_1 2048 d nreg offset v)
  | _ => (pure ())

def decode_FMOPA_ZA_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 => (execute_FMOPA_ZA_PP_ZZ_16 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op)
  | 256 => (execute_FMOPA_ZA_PP_ZZ_16 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op)
  | 512 => (execute_FMOPA_ZA_PP_ZZ_16 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op)
  | 1024 => (execute_FMOPA_ZA_PP_ZZ_16 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op)
  | 2048 => (execute_FMOPA_ZA_PP_ZZ_16 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op)
  | _ => (pure ())

def decode_FMOPS_ZA_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 => (execute_FMOPS_ZA_PP_ZZ_16 128 (((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize) a b da esize m n sub_op)
  | 256 => (execute_FMOPS_ZA_PP_ZZ_16 256 (((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize) a b da esize m n sub_op)
  | 512 => (execute_FMOPS_ZA_PP_ZZ_16 512 (((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize) a b da esize m n sub_op)
  | 1024 => (execute_FMOPS_ZA_PP_ZZ_16 1024 (((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize) a b da esize m n sub_op)
  | 2048 => (execute_FMOPS_ZA_PP_ZZ_16 2048 (((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize) a b da esize m n sub_op)
  | _ => (pure ())

def decode_BFMOPA_ZA_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 => (execute_BFMOPA_ZA_PP_ZZ_16 128 (((Int.ediv 128 16) *i (Int.ediv 128 16)) *i 16) a b da m n sub_op)
  | 256 => (execute_BFMOPA_ZA_PP_ZZ_16 256 (((Int.ediv 256 16) *i (Int.ediv 256 16)) *i 16) a b da m n sub_op)
  | 512 => (execute_BFMOPA_ZA_PP_ZZ_16 512 (((Int.ediv 512 16) *i (Int.ediv 512 16)) *i 16) a b da m n sub_op)
  | 1024 => (execute_BFMOPA_ZA_PP_ZZ_16 1024 (((Int.ediv 1024 16) *i (Int.ediv 1024 16)) *i 16) a b da m n sub_op)
  | 2048 => (execute_BFMOPA_ZA_PP_ZZ_16 2048 (((Int.ediv 2048 16) *i (Int.ediv 2048 16)) *i 16) a b da m n sub_op)
  | _ => (pure ())

def decode_BFMOPS_ZA_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let a := (BitVec.toNat Pn)
  let b := (BitVec.toNat Pm)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 => (execute_BFMOPS_ZA_PP_ZZ_16 128 (((Int.ediv 128 16) *i (Int.ediv 128 16)) *i 16) a b da m n sub_op)
  | 256 => (execute_BFMOPS_ZA_PP_ZZ_16 256 (((Int.ediv 256 16) *i (Int.ediv 256 16)) *i 16) a b da m n sub_op)
  | 512 => (execute_BFMOPS_ZA_PP_ZZ_16 512 (((Int.ediv 512 16) *i (Int.ediv 512 16)) *i 16) a b da m n sub_op)
  | 1024 => (execute_BFMOPS_ZA_PP_ZZ_16 1024 (((Int.ediv 1024 16) *i (Int.ediv 1024 16)) *i 16) a b da m n sub_op)
  | 2048 => (execute_BFMOPS_ZA_PP_ZZ_16 2048 (((Int.ediv 2048 16) *i (Int.ediv 2048 16)) *i 16) a b da m n sub_op)
  | _ => (pure ())

def decode_FADD_ZA_ZW_2x2_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_FADD_ZA_ZW_2x2_16 128 esize m nreg offset v)
  | 256 => (execute_FADD_ZA_ZW_2x2_16 256 esize m nreg offset v)
  | 512 => (execute_FADD_ZA_ZW_2x2_16 512 esize m nreg offset v)
  | 1024 => (execute_FADD_ZA_ZW_2x2_16 1024 esize m nreg offset v)
  | 2048 => (execute_FADD_ZA_ZW_2x2_16 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_FSUB_ZA_ZW_2x2_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_FSUB_ZA_ZW_2x2_16 128 esize m nreg offset v)
  | 256 => (execute_FSUB_ZA_ZW_2x2_16 256 esize m nreg offset v)
  | 512 => (execute_FSUB_ZA_ZW_2x2_16 512 esize m nreg offset v)
  | 1024 => (execute_FSUB_ZA_ZW_2x2_16 1024 esize m nreg offset v)
  | 2048 => (execute_FSUB_ZA_ZW_2x2_16 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_BFADD_ZA_ZW_2x2_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_BFADD_ZA_ZW_2x2_16 128 m nreg offset v)
  | 256 => (execute_BFADD_ZA_ZW_2x2_16 256 m nreg offset v)
  | 512 => (execute_BFADD_ZA_ZW_2x2_16 512 m nreg offset v)
  | 1024 => (execute_BFADD_ZA_ZW_2x2_16 1024 m nreg offset v)
  | 2048 => (execute_BFADD_ZA_ZW_2x2_16 2048 m nreg offset v)
  | _ => (pure ())

def decode_BFSUB_ZA_ZW_2x2_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let nreg := 2
  match VL with
  | 128 => (execute_BFSUB_ZA_ZW_2x2_16 128 m nreg offset v)
  | 256 => (execute_BFSUB_ZA_ZW_2x2_16 256 m nreg offset v)
  | 512 => (execute_BFSUB_ZA_ZW_2x2_16 512 m nreg offset v)
  | 1024 => (execute_BFSUB_ZA_ZW_2x2_16 1024 m nreg offset v)
  | 2048 => (execute_BFSUB_ZA_ZW_2x2_16 2048 m nreg offset v)
  | _ => (pure ())

def decode_FADD_ZA_ZW_4x4_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_FADD_ZA_ZW_4x4_16 128 esize m nreg offset v)
  | 256 => (execute_FADD_ZA_ZW_4x4_16 256 esize m nreg offset v)
  | 512 => (execute_FADD_ZA_ZW_4x4_16 512 esize m nreg offset v)
  | 1024 => (execute_FADD_ZA_ZW_4x4_16 1024 esize m nreg offset v)
  | 2048 => (execute_FADD_ZA_ZW_4x4_16 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_FSUB_ZA_ZW_4x4_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_FSUB_ZA_ZW_4x4_16 128 esize m nreg offset v)
  | 256 => (execute_FSUB_ZA_ZW_4x4_16 256 esize m nreg offset v)
  | 512 => (execute_FSUB_ZA_ZW_4x4_16 512 esize m nreg offset v)
  | 1024 => (execute_FSUB_ZA_ZW_4x4_16 1024 esize m nreg offset v)
  | 2048 => (execute_FSUB_ZA_ZW_4x4_16 2048 esize m nreg offset v)
  | _ => (pure ())

def decode_BFADD_ZA_ZW_4x4_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_BFADD_ZA_ZW_4x4_16 128 m nreg offset v)
  | 256 => (execute_BFADD_ZA_ZW_4x4_16 256 m nreg offset v)
  | 512 => (execute_BFADD_ZA_ZW_4x4_16 512 m nreg offset v)
  | 1024 => (execute_BFADD_ZA_ZW_4x4_16 1024 m nreg offset v)
  | 2048 => (execute_BFADD_ZA_ZW_4x4_16 2048 m nreg offset v)
  | _ => (pure ())

def decode_BFSUB_ZA_ZW_4x4_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let nreg := 4
  match VL with
  | 128 => (execute_BFSUB_ZA_ZW_4x4_16 128 m nreg offset v)
  | 256 => (execute_BFSUB_ZA_ZW_4x4_16 256 m nreg offset v)
  | 512 => (execute_BFSUB_ZA_ZW_4x4_16 512 m nreg offset v)
  | 1024 => (execute_BFSUB_ZA_ZW_4x4_16 1024 m nreg offset v)
  | 2048 => (execute_BFSUB_ZA_ZW_4x4_16 2048 m nreg offset v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZW_2x2_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_FMLA_ZA_ZZW_2x2_16 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZW_2x2_16 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZW_2x2_16 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZW_2x2_16 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZW_2x2_16 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZW_2x2_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_FMLS_ZA_ZZW_2x2_16 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZW_2x2_16 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZW_2x2_16 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZW_2x2_16 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZW_2x2_16 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLA_ZA_ZZW_2x2_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLA_ZA_ZZW_2x2_16 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLA_ZA_ZZW_2x2_16 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLA_ZA_ZZW_2x2_16 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLA_ZA_ZZW_2x2_16 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLA_ZA_ZZW_2x2_16 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLS_ZA_ZZW_2x2_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLS_ZA_ZZW_2x2_16 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLS_ZA_ZZW_2x2_16 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLS_ZA_ZZW_2x2_16 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLS_ZA_ZZW_2x2_16 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLS_ZA_ZZW_2x2_16 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZV_2x1_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_FMLA_ZA_ZZV_2x1_16 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZV_2x1_16 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZV_2x1_16 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZV_2x1_16 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZV_2x1_16 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZV_2x1_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_FMLS_ZA_ZZV_2x1_16 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZV_2x1_16 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZV_2x1_16 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZV_2x1_16 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZV_2x1_16 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLA_ZA_ZZV_2x1_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLA_ZA_ZZV_2x1_16 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLA_ZA_ZZV_2x1_16 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLA_ZA_ZZV_2x1_16 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLA_ZA_ZZV_2x1_16 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLA_ZA_ZZV_2x1_16 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLS_ZA_ZZV_2x1_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLS_ZA_ZZV_2x1_16 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLS_ZA_ZZV_2x1_16 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLS_ZA_ZZV_2x1_16 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLS_ZA_ZZV_2x1_16 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLS_ZA_ZZV_2x1_16 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZW_4x4_16 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_FMLA_ZA_ZZW_4x4_16 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZW_4x4_16 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZW_4x4_16 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZW_4x4_16 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZW_4x4_16 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZW_4x4_16 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_FMLS_ZA_ZZW_4x4_16 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZW_4x4_16 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZW_4x4_16 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZW_4x4_16 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZW_4x4_16 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLA_ZA_ZZW_4x4_16 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLA_ZA_ZZW_4x4_16 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLA_ZA_ZZW_4x4_16 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLA_ZA_ZZW_4x4_16 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLA_ZA_ZZW_4x4_16 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLA_ZA_ZZW_4x4_16 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLS_ZA_ZZW_4x4_16 (sz : (BitVec 1)) (Zm : (BitVec 3)) (Rv : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLS_ZA_ZZW_4x4_16 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLS_ZA_ZZW_4x4_16 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLS_ZA_ZZW_4x4_16 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLS_ZA_ZZW_4x4_16 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLS_ZA_ZZW_4x4_16 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZV_4x1_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_FMLA_ZA_ZZV_4x1_16 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZV_4x1_16 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZV_4x1_16 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZV_4x1_16 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZV_4x1_16 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZV_4x1_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_FMLS_ZA_ZZV_4x1_16 128 esize m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZV_4x1_16 256 esize m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZV_4x1_16 512 esize m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZV_4x1_16 1024 esize m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZV_4x1_16 2048 esize m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLA_ZA_ZZV_4x1_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLA_ZA_ZZV_4x1_16 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLA_ZA_ZZV_4x1_16 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLA_ZA_ZZV_4x1_16 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLA_ZA_ZZV_4x1_16 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLA_ZA_ZZV_4x1_16 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLS_ZA_ZZV_4x1_16 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLS_ZA_ZZV_4x1_16 128 m n nreg offset sub_op v)
  | 256 => (execute_BFMLS_ZA_ZZV_4x1_16 256 m n nreg offset sub_op v)
  | 512 => (execute_BFMLS_ZA_ZZV_4x1_16 512 m n nreg offset sub_op v)
  | 1024 => (execute_BFMLS_ZA_ZZV_4x1_16 1024 m n nreg offset sub_op v)
  | 2048 => (execute_BFMLS_ZA_ZZV_4x1_16 2048 m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZi_H2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_FMLA_ZA_ZZi_H2xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZi_H2xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZi_H2xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZi_H2xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZi_H2xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZi_H2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_FMLS_ZA_ZZi_H2xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZi_H2xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZi_H2xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZi_H2xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZi_H2xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLA_ZA_ZZi_H2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLA_ZA_ZZi_H2xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_BFMLA_ZA_ZZi_H2xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_BFMLA_ZA_ZZi_H2xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_BFMLA_ZA_ZZi_H2xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_BFMLA_ZA_ZZi_H2xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLS_ZA_ZZi_H2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg := 2
  match VL with
  | 128 => (execute_BFMLS_ZA_ZZi_H2xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_BFMLS_ZA_ZZi_H2xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_BFMLS_ZA_ZZi_H2xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_BFMLS_ZA_ZZi_H2xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_BFMLS_ZA_ZZi_H2xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLA_ZA_ZZi_H4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_FMLA_ZA_ZZi_H4xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLA_ZA_ZZi_H4xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLA_ZA_ZZi_H4xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLA_ZA_ZZi_H4xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLA_ZA_ZZi_H4xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_FMLS_ZA_ZZi_H4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_FMLS_ZA_ZZi_H4xi 128 esize index m n nreg offset sub_op v)
  | 256 => (execute_FMLS_ZA_ZZi_H4xi 256 esize index m n nreg offset sub_op v)
  | 512 => (execute_FMLS_ZA_ZZi_H4xi 512 esize index m n nreg offset sub_op v)
  | 1024 => (execute_FMLS_ZA_ZZi_H4xi 1024 esize index m n nreg offset sub_op v)
  | 2048 => (execute_FMLS_ZA_ZZi_H4xi 2048 esize index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLA_ZA_ZZi_H4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := false
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLA_ZA_ZZi_H4xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_BFMLA_ZA_ZZi_H4xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_BFMLA_ZA_ZZi_H4xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_BFMLA_ZA_ZZi_H4xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_BFMLA_ZA_ZZi_H4xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMLS_ZA_ZZi_H4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i3h : (BitVec 2)) (Zn : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let v := (BitVec.toNat (0b010#3 +++ Rv))
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let offset := (BitVec.toNat off3)
  let index := (BitVec.toNat (i3h +++ i3l))
  let sub_op : Bool := true
  let nreg := 4
  match VL with
  | 128 => (execute_BFMLS_ZA_ZZi_H4xi 128 index m n nreg offset sub_op v)
  | 256 => (execute_BFMLS_ZA_ZZi_H4xi 256 index m n nreg offset sub_op v)
  | 512 => (execute_BFMLS_ZA_ZZi_H4xi 512 index m n nreg offset sub_op v)
  | 1024 => (execute_BFMLS_ZA_ZZi_H4xi 1024 index m n nreg offset sub_op v)
  | 2048 => (execute_BFMLS_ZA_ZZi_H4xi 2048 index m n nreg offset sub_op v)
  | _ => (pure ())

def decode_BFMAX_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_BFMAX_MZ_ZZW_2x2 128 dn m nreg)
  | 256 => (execute_BFMAX_MZ_ZZW_2x2 256 dn m nreg)
  | 512 => (execute_BFMAX_MZ_ZZW_2x2 512 dn m nreg)
  | 1024 => (execute_BFMAX_MZ_ZZW_2x2 1024 dn m nreg)
  | 2048 => (execute_BFMAX_MZ_ZZW_2x2 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMAX_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_BFMAX_MZ_ZZV_2x1 128 dn m nreg)
  | 256 => (execute_BFMAX_MZ_ZZV_2x1 256 dn m nreg)
  | 512 => (execute_BFMAX_MZ_ZZV_2x1 512 dn m nreg)
  | 1024 => (execute_BFMAX_MZ_ZZV_2x1 1024 dn m nreg)
  | 2048 => (execute_BFMAX_MZ_ZZV_2x1 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMIN_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_BFMIN_MZ_ZZW_2x2 128 dn m nreg)
  | 256 => (execute_BFMIN_MZ_ZZW_2x2 256 dn m nreg)
  | 512 => (execute_BFMIN_MZ_ZZW_2x2 512 dn m nreg)
  | 1024 => (execute_BFMIN_MZ_ZZW_2x2 1024 dn m nreg)
  | 2048 => (execute_BFMIN_MZ_ZZW_2x2 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMIN_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_BFMIN_MZ_ZZV_2x1 128 dn m nreg)
  | 256 => (execute_BFMIN_MZ_ZZV_2x1 256 dn m nreg)
  | 512 => (execute_BFMIN_MZ_ZZV_2x1 512 dn m nreg)
  | 1024 => (execute_BFMIN_MZ_ZZV_2x1 1024 dn m nreg)
  | 2048 => (execute_BFMIN_MZ_ZZV_2x1 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMAX_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_BFMAX_MZ_ZZW_4x4 128 dn m nreg)
  | 256 => (execute_BFMAX_MZ_ZZW_4x4 256 dn m nreg)
  | 512 => (execute_BFMAX_MZ_ZZW_4x4 512 dn m nreg)
  | 1024 => (execute_BFMAX_MZ_ZZW_4x4 1024 dn m nreg)
  | 2048 => (execute_BFMAX_MZ_ZZW_4x4 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMAX_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_BFMAX_MZ_ZZV_4x1 128 dn m nreg)
  | 256 => (execute_BFMAX_MZ_ZZV_4x1 256 dn m nreg)
  | 512 => (execute_BFMAX_MZ_ZZV_4x1 512 dn m nreg)
  | 1024 => (execute_BFMAX_MZ_ZZV_4x1 1024 dn m nreg)
  | 2048 => (execute_BFMAX_MZ_ZZV_4x1 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMIN_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_BFMIN_MZ_ZZW_4x4 128 dn m nreg)
  | 256 => (execute_BFMIN_MZ_ZZW_4x4 256 dn m nreg)
  | 512 => (execute_BFMIN_MZ_ZZW_4x4 512 dn m nreg)
  | 1024 => (execute_BFMIN_MZ_ZZW_4x4 1024 dn m nreg)
  | 2048 => (execute_BFMIN_MZ_ZZW_4x4 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMIN_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_BFMIN_MZ_ZZV_4x1 128 dn m nreg)
  | 256 => (execute_BFMIN_MZ_ZZV_4x1 256 dn m nreg)
  | 512 => (execute_BFMIN_MZ_ZZV_4x1 512 dn m nreg)
  | 1024 => (execute_BFMIN_MZ_ZZV_4x1 1024 dn m nreg)
  | 2048 => (execute_BFMIN_MZ_ZZV_4x1 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMAXNM_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_BFMAXNM_MZ_ZZW_2x2 128 dn m nreg)
  | 256 => (execute_BFMAXNM_MZ_ZZW_2x2 256 dn m nreg)
  | 512 => (execute_BFMAXNM_MZ_ZZW_2x2 512 dn m nreg)
  | 1024 => (execute_BFMAXNM_MZ_ZZW_2x2 1024 dn m nreg)
  | 2048 => (execute_BFMAXNM_MZ_ZZW_2x2 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMAXNM_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_BFMAXNM_MZ_ZZV_2x1 128 dn m nreg)
  | 256 => (execute_BFMAXNM_MZ_ZZV_2x1 256 dn m nreg)
  | 512 => (execute_BFMAXNM_MZ_ZZV_2x1 512 dn m nreg)
  | 1024 => (execute_BFMAXNM_MZ_ZZV_2x1 1024 dn m nreg)
  | 2048 => (execute_BFMAXNM_MZ_ZZV_2x1 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMINNM_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (Zm +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_BFMINNM_MZ_ZZW_2x2 128 dn m nreg)
  | 256 => (execute_BFMINNM_MZ_ZZW_2x2 256 dn m nreg)
  | 512 => (execute_BFMINNM_MZ_ZZW_2x2 512 dn m nreg)
  | 1024 => (execute_BFMINNM_MZ_ZZW_2x2 1024 dn m nreg)
  | 2048 => (execute_BFMINNM_MZ_ZZW_2x2 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMINNM_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0#1))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 2
  match VL with
  | 128 => (execute_BFMINNM_MZ_ZZV_2x1 128 dn m nreg)
  | 256 => (execute_BFMINNM_MZ_ZZV_2x1 256 dn m nreg)
  | 512 => (execute_BFMINNM_MZ_ZZV_2x1 512 dn m nreg)
  | 1024 => (execute_BFMINNM_MZ_ZZV_2x1 1024 dn m nreg)
  | 2048 => (execute_BFMINNM_MZ_ZZV_2x1 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMAXNM_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_BFMAXNM_MZ_ZZW_4x4 128 dn m nreg)
  | 256 => (execute_BFMAXNM_MZ_ZZW_4x4 256 dn m nreg)
  | 512 => (execute_BFMAXNM_MZ_ZZW_4x4 512 dn m nreg)
  | 1024 => (execute_BFMAXNM_MZ_ZZW_4x4 1024 dn m nreg)
  | 2048 => (execute_BFMAXNM_MZ_ZZW_4x4 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMAXNM_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_BFMAXNM_MZ_ZZV_4x1 128 dn m nreg)
  | 256 => (execute_BFMAXNM_MZ_ZZV_4x1 256 dn m nreg)
  | 512 => (execute_BFMAXNM_MZ_ZZV_4x1 512 dn m nreg)
  | 1024 => (execute_BFMAXNM_MZ_ZZV_4x1 1024 dn m nreg)
  | 2048 => (execute_BFMAXNM_MZ_ZZV_4x1 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMINNM_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_BFMINNM_MZ_ZZW_4x4 128 dn m nreg)
  | 256 => (execute_BFMINNM_MZ_ZZW_4x4 256 dn m nreg)
  | 512 => (execute_BFMINNM_MZ_ZZW_4x4 512 dn m nreg)
  | 1024 => (execute_BFMINNM_MZ_ZZW_4x4 1024 dn m nreg)
  | 2048 => (execute_BFMINNM_MZ_ZZW_4x4 2048 dn m nreg)
  | _ => (pure ())

def decode_BFMINNM_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat (Zdn +++ 0b00#2))
  let m := (BitVec.toNat (0#1 +++ Zm))
  let nreg := 4
  match VL with
  | 128 => (execute_BFMINNM_MZ_ZZV_4x1 128 dn m nreg)
  | 256 => (execute_BFMINNM_MZ_ZZV_4x1 256 dn m nreg)
  | 512 => (execute_BFMINNM_MZ_ZZV_4x1 512 dn m nreg)
  | 1024 => (execute_BFMINNM_MZ_ZZV_4x1 1024 dn m nreg)
  | 2048 => (execute_BFMINNM_MZ_ZZV_4x1 2048 dn m nreg)
  | _ => (pure ())

def decode_FCVT_MZ2_Z__ (Zn : (BitVec 5)) (Zd : (BitVec 4)) (L : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 => (execute_FCVT_MZ2_Z__ 128 d n)
  | 256 => (execute_FCVT_MZ2_Z__ 256 d n)
  | 512 => (execute_FCVT_MZ2_Z__ 512 d n)
  | 1024 => (execute_FCVT_MZ2_Z__ 1024 d n)
  | 2048 => (execute_FCVT_MZ2_Z__ 2048 d n)
  | _ => (pure ())

def decode_FCVTL_MZ2_Z__ (Zn : (BitVec 5)) (Zd : (BitVec 4)) (L : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEF16F16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 => (execute_FCVTL_MZ2_Z__ 128 d n)
  | 256 => (execute_FCVTL_MZ2_Z__ 256 d n)
  | 512 => (execute_FCVTL_MZ2_Z__ 512 d n)
  | 1024 => (execute_FCVTL_MZ2_Z__ 1024 d n)
  | 2048 => (execute_FCVTL_MZ2_Z__ 2048 d n)
  | _ => (pure ())

def decode_BFCLAMP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0#1))
  let nreg := 2
  match VL with
  | 128 => (execute_BFCLAMP_MZ_ZZ_2 128 d m n nreg)
  | 256 => (execute_BFCLAMP_MZ_ZZ_2 256 d m n nreg)
  | 512 => (execute_BFCLAMP_MZ_ZZ_2 512 d m n nreg)
  | 1024 => (execute_BFCLAMP_MZ_ZZ_2 1024 d m n nreg)
  | 2048 => (execute_BFCLAMP_MZ_ZZ_2 2048 d m n nreg)
  | _ => (pure ())

def decode_BFCLAMP_MZ_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSMEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg := 4
  match VL with
  | 128 => (execute_BFCLAMP_MZ_ZZ_4 128 d m n nreg)
  | 256 => (execute_BFCLAMP_MZ_ZZ_4 256 d m n nreg)
  | 512 => (execute_BFCLAMP_MZ_ZZ_4 512 d m n nreg)
  | 1024 => (execute_BFCLAMP_MZ_ZZ_4 1024 d m n nreg)
  | 2048 => (execute_BFCLAMP_MZ_ZZ_4 2048 d m n nreg)
  | _ => (pure ())

